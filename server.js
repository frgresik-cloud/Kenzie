const express = require('express');
const http = require('http');
const WebSocket = require('ws');
const path = require('path');
const bodyParser = require('body-parser');
const fs = require('fs');
const multer = require('multer');
const crypto = require('crypto');

const app = express();
const server = http.createServer(app);
const wss = new WebSocket.Server({ server, maxPayload: 200 * 1024 * 1024 });

app.use(bodyParser.json({ limit: '60mb' }));
app.use(express.static(__dirname));

const DATA_DIR = process.env.DATA_DIR || __dirname;
if (!fs.existsSync(DATA_DIR)) fs.mkdirSync(DATA_DIR, { recursive: true });

const DB_FILE = path.join(DATA_DIR, 'chat.json');
const UPLOAD_DIR = path.join(DATA_DIR, 'uploads');
if (!fs.existsSync(UPLOAD_DIR)) fs.mkdirSync(UPLOAD_DIR, { recursive: true });

const FILE_TTL_MS = 24 * 60 * 60 * 1000;
const STATUS_TTL_MS = 24 * 60 * 60 * 1000;
const CALL_TIMEOUT_MS = 60 * 1000;

let db = { users: {}, chats: {}, groups: {}, unread: {}, blocks: {}, statuses: {}, contacts: {} };
if (fs.existsSync(DB_FILE)) {
    try {
        const loaded = JSON.parse(fs.readFileSync(DB_FILE, 'utf8'));
        db.users = loaded.users || {};
        db.chats = loaded.chats || {};
        db.groups = loaded.groups || {};
        db.unread = loaded.unread || {};
        db.blocks = loaded.blocks || {};
        db.statuses = loaded.statuses || {};
        db.contacts = loaded.contacts || {};
    } catch (e) { console.error('DB corrupt:', e.message); }
}
if (!db.contacts) db.contacts = {};
Object.keys(db.users).forEach(k => {
    if (typeof db.users[k] === 'string') db.users[k] = { password: db.users[k], bio: '', avatar: null, displayName: '', lastSeen: null, created: Date.now(), introDismissed: [] };
    if (db.users[k].displayName === undefined) db.users[k].displayName = '';
    if (db.users[k].lastSeen === undefined) db.users[k].lastSeen = null;
    if (!Array.isArray(db.users[k].introDismissed)) db.users[k].introDismissed = [];
});

function saveDB() {
    try { fs.writeFileSync(DB_FILE, JSON.stringify(db, null, 2)); }
    catch (e) { console.error('Save error:', e); }
}
function uid(n = 10) { return crypto.randomBytes(n).toString('hex'); }
function getChatId(a, b) { return [a, b].sort().join('_'); }
function groupChatId(id) { return 'grp_' + id; }
function nowTime() { return new Date().toLocaleTimeString('id-ID', { hour: '2-digit', minute: '2-digit', hour12: false }); }

function getSavedName(me, target) {
    if (!db.contacts[me]) return null;
    return db.contacts[me][target] || null;
}
function isSavedBy(me, target) {
    if (!db.contacts[me]) return false;
    return !!db.contacts[me][target];
}
function isMutualSave(a, b) { return isSavedBy(a, b) && isSavedBy(b, a); }
function getDisplayNameFor(me, target) {
    const saved = getSavedName(me, target);
    if (saved) return saved;
    return (db.users[target]?.displayName || target);
}

function usernameTaken(u, exceptGroupId) {
    if (db.users[u]) return true;
    return Object.values(db.groups).some(g => g.username === u && g.id !== exceptGroupId);
}

function purgeExpiredStatuses() {
    const now = Date.now();
    let changed = false;
    Object.keys(db.statuses).forEach(u => {
        const before = (db.statuses[u] || []).length;
        db.statuses[u] = (db.statuses[u] || []).filter(s => (s.expiresAt || 0) > now);
        if (db.statuses[u].length !== before) changed = true;
    });
    if (changed) saveDB();
}

function cleanupExpired() {
    const now = Date.now();
    let changed = false;
    Object.keys(db.chats).forEach(cid => {
        const msgs = db.chats[cid];
        if (!Array.isArray(msgs)) return;
        msgs.forEach(m => {
            if (m.file && m.file.url && !m.file.expired) {
                const exp = m.file.expiresAt || ((m.file.uploadedAt || 0) + FILE_TTL_MS);
                if (now >= exp) {
                    try { const fp = path.join(UPLOAD_DIR, path.basename(m.file.url)); if (fs.existsSync(fp)) fs.unlinkSync(fp); } catch (e) {}
                    m.file.expired = true; delete m.file.url; changed = true;
                }
            }
        });
    });
    Object.keys(db.statuses).forEach(u => {
        const arr = db.statuses[u] || [];
        const filtered = arr.filter(s => (s.expiresAt || 0) > now);
        if (filtered.length !== arr.length) { db.statuses[u] = filtered; changed = true; }
    });
    if (changed) saveDB();
}
setInterval(cleanupExpired, 30 * 60 * 1000);
cleanupExpired();

function migrateUsername(oldU, newU) {
    if (!db.users[oldU]) return { success: false, msg: 'User tidak ditemukan' };
    if (db.users[newU]) return { success: false, msg: 'Username sudah dipakai' };

    db.users[newU] = db.users[oldU];
    delete db.users[oldU];

    const newChats = {};
    Object.keys(db.chats).forEach(cid => {
        let newCid = cid;
        if (!cid.startsWith('grp_')) {
            const parts = cid.split('_');
            if (parts.includes(oldU)) {
                const other = parts.find(p => p !== oldU);
                newCid = [newU, other].sort().join('_');
            }
        }
        db.chats[cid].forEach(m => {
            if (m.from === oldU) m.from = newU;
            if (m.to === oldU) m.to = newU;
            if (Array.isArray(m.readBy)) m.readBy = m.readBy.map(x => x === oldU ? newU : x);
            if (Array.isArray(m.deletedFor)) m.deletedFor = m.deletedFor.map(x => x === oldU ? newU : x);
        });
        newChats[newCid] = db.chats[cid];
    });
    db.chats = newChats;

    Object.values(db.groups).forEach(g => {
        if (g.owner === oldU) g.owner = newU;
        g.admins = g.admins.map(x => x === oldU ? newU : x);
        g.members = g.members.map(x => x === oldU ? newU : x);
    });

    const oldBlocks = db.blocks[oldU] || [];
    delete db.blocks[oldU];
    db.blocks[newU] = oldBlocks;
    Object.keys(db.blocks).forEach(k => { db.blocks[k] = db.blocks[k].map(x => x === oldU ? newU : x); });

    const oldContacts = db.contacts[oldU] || {};
    delete db.contacts[oldU];
    db.contacts[newU] = oldContacts;
    Object.keys(db.contacts).forEach(k => {
        const obj = db.contacts[k];
        if (obj[oldU] !== undefined) { obj[newU] = obj[oldU]; delete obj[oldU]; }
    });

    Object.keys(db.users).forEach(u => {
        if (Array.isArray(db.users[u].introDismissed)) {
            db.users[u].introDismissed = db.users[u].introDismissed.map(x => x === oldU ? newU : x);
        }
    });

    if (db.statuses[oldU]) { db.statuses[newU] = db.statuses[oldU]; delete db.statuses[oldU]; }
    Object.keys(db.statuses).forEach(k => {
        db.statuses[k].forEach(s => { if (Array.isArray(s.views)) s.views = s.views.map(x => x === oldU ? newU : x); });
    });

    if (db.unread[oldU]) { db.unread[newU] = db.unread[oldU]; delete db.unread[oldU]; }
    Object.keys(db.unread).forEach(k => {
        const obj = db.unread[k];
        if (obj[oldU] !== undefined) { obj[newU] = obj[oldU]; delete obj[oldU]; }
    });

    saveDB();
    return { success: true };
}

const storage = multer.diskStorage({
    destination: (req, f, cb) => cb(null, UPLOAD_DIR),
    filename: (req, f, cb) => { cb(null, Date.now() + '_' + uid(6) + (path.extname(f.originalname) || '')); }
});
const upload = multer({ storage, limits: { fileSize: 200 * 1024 * 1024 } });
app.use('/uploads', express.static(UPLOAD_DIR));

app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'index.html')));
app.get('/login', (req, res) => res.sendFile(path.join(__dirname, 'login.html')));
app.get('/health', (req, res) => res.status(200).json({ ok: true, ts: Date.now() }));

function displayOf(u) {
    if (!db.users[u]) return u;
    return db.users[u].displayName || u;
}
function isUserOnline(u) {
    const c = onlineClients[u];
    return !!(c && c.readyState === WebSocket.OPEN);
}
function publicUser(u) {
    const user = db.users[u] || {};
    return {
        username: u,
        displayName: user.displayName || '',
        bio: user.bio || '',
        avatar: user.avatar || null,
        lastSeen: isUserOnline(u) ? null : (user.lastSeen || null),
        isOnline: isUserOnline(u)
    };
}

app.post('/api/register', (req, res) => {
    const { username, password } = req.body;
    if (!username || !password) return res.json({ success: false, msg: 'Kolom tidak boleh kosong!' });
    const u = username.trim().toLowerCase();
    if (!/^[a-z0-9_.-]{3,20}$/.test(u)) return res.json({ success: false, msg: 'Username 3-20 karakter (huruf kecil, angka, . _ -)' });
    if (usernameTaken(u)) return res.json({ success: false, msg: 'Username ini telah digunakan!' });
    db.users[u] = { password, bio: '', avatar: null, displayName: '', lastSeen: null, created: Date.now(), introDismissed: [] };
    saveDB();
    res.json({ success: true, msg: 'Pendaftaran berhasil!' });
});
app.post('/api/login', (req, res) => {
    const { username, password } = req.body;
    const u = (username || '').trim().toLowerCase();
    if (db.users[u] && db.users[u].password === password) {
        return res.json({ success: true, user: publicUser(u) });
    }
    res.json({ success: false, msg: 'Username atau Password salah!' });
});
app.get('/api/me/:username', (req, res) => {
    const u = req.params.username.toLowerCase();
    if (!db.users[u]) return res.json({ exists: false });
    res.json({ exists: true, user: publicUser(u) });
});
app.post('/api/change-password', (req, res) => {
    const { username, oldPassword, newPassword } = req.body;
    const u = (username || '').toLowerCase();
    if (!db.users[u]) return res.json({ success: false, msg: 'User tidak ditemukan' });
    if (db.users[u].password !== oldPassword) return res.json({ success: false, msg: 'Password lama salah!' });
    if (!newPassword || newPassword.length < 3) return res.json({ success: false, msg: 'Password baru minimal 3 karakter' });
    db.users[u].password = newPassword; saveDB();
    res.json({ success: true, msg: 'Password diubah!' });
});
app.post('/api/change-username', (req, res) => {
    const { username, newUsername } = req.body;
    const oldU = (username || '').trim().toLowerCase();
    const newU = (newUsername || '').trim().toLowerCase();

    if (!newU) return res.json({ success: false, msg: 'Username wajib diisi' });
    if (!/^[a-z0-9_.-]{3,20}$/.test(newU)) return res.json({ success: false, msg: 'Username 3-20 karakter' });
    if (newU === oldU) return res.json({ success: false, msg: 'Sama dengan username lama' });
    if (!db.users[oldU]) return res.json({ success: false, msg: 'User tidak ditemukan' });
    if (usernameTaken(newU)) return res.json({ success: false, msg: 'Username ini telah digunakan!' });

    const r = migrateUsername(oldU, newU);
    if (!r.success) return res.json(r);

    if (onlineClients[oldU]) { onlineClients[newU] = onlineClients[oldU]; delete onlineClients[oldU]; }
    if (viewing[oldU] !== undefined) { viewing[newU] = viewing[oldU]; delete viewing[oldU]; }

    Object.keys(db.users).forEach(u => sendToUser(u, { type: 'chatlist' }));
    sendToUser(newU, { type: 'username_changed', newUsername: newU, oldUsername: oldU });
    res.json({ success: true, newUsername: newU, oldUsername: oldU });
});
app.post('/api/group/change-member-username', (req, res) => {
    const { username, groupId, target, newUsername } = req.body;
    const u = (username || '').toLowerCase();
    const t = (target || '').toLowerCase();
    const nu = (newUsername || '').trim().toLowerCase();
    const g = db.groups[groupId];

    if (!g) return res.json({ success: false, msg: 'Grup tidak ditemukan' });
    if (!g.members.includes(u)) return res.json({ success: false, msg: 'Kamu bukan member grup' });
    const isOwner = g.owner === u;
    const isAdmin = g.admins.includes(u);
    if (!isOwner && !isAdmin) return res.json({ success: false, msg: 'Hanya pemilik / admin yang bisa ubah username' });
    if (!g.members.includes(t)) return res.json({ success: false, msg: 'Target bukan anggota grup' });
    if (!nu) return res.json({ success: false, msg: 'Username wajib diisi' });
    if (!/^[a-z0-9_.-]{3,20}$/.test(nu)) return res.json({ success: false, msg: 'Username 3-20 karakter' });
    if (nu === t) return res.json({ success: false, msg: 'Sama dengan username lama' });
    if (usernameTaken(nu)) return res.json({ success: false, msg: 'Username ini telah digunakan!' });

    const r = migrateUsername(t, nu);
    if (!r.success) return res.json(r);

    if (onlineClients[t]) { onlineClients[nu] = onlineClients[t]; delete onlineClients[t]; }
    if (viewing[t] !== undefined) { viewing[nu] = viewing[t]; delete viewing[t]; }

    broadcastToGroup(groupId, { type: 'group_updated', group: sanitizeGroup(g) });
    Object.keys(db.users).forEach(u => sendToUser(u, { type: 'chatlist' }));
    sendToUser(nu, { type: 'username_changed', newUsername: nu, oldUsername: t });
    res.json({ success: true, newUsername: nu, oldUsername: t });
});

app.post('/api/contact/save', (req, res) => {
    const { username, target, savedAs } = req.body;
    const u = (username || '').toLowerCase();
    const t = (target || '').toLowerCase();
    if (!db.users[u] || !db.users[t] || u === t) return res.json({ success: false, msg: 'Tidak valid' });
    const name = (savedAs || '').trim().slice(0, 60);
    if (!name) return res.json({ success: false, msg: 'Nama wajib diisi' });
    if (!db.contacts[u]) db.contacts[u] = {};
    db.contacts[u][t] = name;
    db.users[u].introDismissed = (db.users[u].introDismissed || []).filter(x => x !== t);
    saveDB();
    sendToUser(u, { type: 'chatlist' });
    sendToUser(t, { type: 'chatlist' });
    sendToUser(u, { type: 'contact_update', target: t, savedAs: name, action: 'save' });
    sendToUser(t, { type: 'contact_update', target: u, action: 'savedByOther' });
    res.json({ success: true, savedAs: name });
});
app.post('/api/contact/delete', (req, res) => {
    const { username, target } = req.body;
    const u = (username || '').toLowerCase();
    const t = (target || '').toLowerCase();
    if (!db.contacts[u]) return res.json({ success: false });
    delete db.contacts[u][t];
    saveDB();
    sendToUser(u, { type: 'chatlist' });
    sendToUser(t, { type: 'chatlist' });
    sendToUser(u, { type: 'contact_update', target: t, action: 'delete' });
    sendToUser(t, { type: 'contact_update', target: u, action: 'deletedByOther' });
    res.json({ success: true });
});
app.get('/api/contact/:username/:target', (req, res) => {
    const u = req.params.username.toLowerCase();
    const t = req.params.target.toLowerCase();
    if (!db.users[u] || !db.users[t]) return res.json({ exists: false });
    const savedAs = getSavedName(u, t);
    const savedByMe = isSavedBy(u, t);
    const savedByThem = isSavedBy(t, u);
    const introDismissed = (db.users[u].introDismissed || []).includes(t);
    const displayName = db.users[t].displayName || '';
    res.json({ savedAs, savedByMe, savedByThem, mutual: savedByMe && savedByThem, introDismissed, displayName });
});
app.post('/api/intro/dismiss', (req, res) => {
    const { username, target } = req.body;
    const u = (username || '').toLowerCase();
    const t = (target || '').toLowerCase();
    if (!db.users[u]) return res.json({ success: false });
    if (!Array.isArray(db.users[u].introDismissed)) db.users[u].introDismissed = [];
    if (!db.users[u].introDismissed.includes(t)) db.users[u].introDismissed.push(t);
    saveDB();
    res.json({ success: true });
});
app.get('/api/contacts/:username', (req, res) => {
    const u = req.params.username.toLowerCase();
    res.json({ contacts: db.contacts[u] || {} });
});

app.get('/api/profile/:username', (req, res) => {
    const u = req.params.username.toLowerCase();
    const viewer = (req.query.viewer || '').toLowerCase();
    if (!db.users[u]) return res.json({ exists: false });
    let avatar = db.users[u].avatar || null;
    let blockedByMe = false, blockedMe = false;
    if (viewer && viewer !== u) {
        blockedByMe = (db.blocks[viewer] || []).includes(u);
        blockedMe = (db.blocks[u] || []).includes(viewer);
    }
    if (blockedByMe || blockedMe) avatar = null;
    const savedAs = viewer ? getSavedName(viewer, u) : null;
    const savedByMe = viewer ? isSavedBy(viewer, u) : false;
    const savedByThem = viewer ? isSavedBy(u, viewer) : false;
    res.json({
        exists: true,
        username: u,
        displayName: db.users[u].displayName || '',
        bio: db.users[u].bio || '',
        avatar,
        blockedByMe,
        blockedMe,
        isOnline: isUserOnline(u),
        lastSeen: isUserOnline(u) ? null : (db.users[u].lastSeen || null),
        savedAs, savedByMe, savedByThem,
        mutual: savedByMe && savedByThem
    });
});
app.post('/api/profile', (req, res) => {
    const { username, bio, avatar, displayName } = req.body;
    const u = (username || '').toLowerCase();
    if (!db.users[u]) return res.json({ success: false });
    if (typeof bio === 'string') db.users[u].bio = bio.slice(0, 150);
    if (avatar !== undefined) db.users[u].avatar = avatar;
    if (typeof displayName === 'string') db.users[u].displayName = displayName.slice(0, 40);
    saveDB();
    broadcastProfileUpdate(u);
    res.json({ success: true, user: publicUser(u) });
});
function broadcastProfileUpdate(u) {
    Object.keys(onlineClients).forEach(other => {
        if (other === u) return;
        sendToUser(other, {
            type: 'profile_updated',
            user: u,
            displayName: db.users[u].displayName || '',
            avatar: db.users[u].avatar || null
        });
    });
}

app.get('/api/search', (req, res) => {
    const q = (req.query.q || '').trim().toLowerCase();
    const viewer = (req.query.exclude || '').toLowerCase();
    if (!q) return res.json({ results: [] });

    const users = Object.keys(db.users)
        .filter(u => u !== viewer)
        .filter(u => {
            const un = u.toLowerCase();
            const dn = (db.users[u].displayName || '').toLowerCase();
            const sv = (getSavedName(viewer, u) || '').toLowerCase();
            return un.includes(q) || dn.includes(q) || sv.includes(q);
        })
        .sort((a, b) => {
            const aExact = a === q ? 0 : (a.startsWith(q) ? 1 : 2);
            const bExact = b === q ? 0 : (b.startsWith(q) ? 1 : 2);
            return aExact - bExact;
        })
        .map(u => ({
            type: 'user',
            username: u,
            displayName: db.users[u].displayName || '',
            bio: db.users[u].bio || '',
            avatar: db.users[u].avatar || null,
            savedAs: getSavedName(viewer, u) || null
        }));

    const groups = Object.values(db.groups)
        .filter(g => {
            if (g.isPrivate && !g.members.includes(viewer)) return false;
            const gu = (g.username || '').toLowerCase();
            const gn = (g.name || '').toLowerCase();
            return gu.includes(q) || gn.includes(q);
        })
        .sort((a, b) => {
            const aExact = (a.username === q || (a.name||'').toLowerCase() === q) ? 0 : 1;
            const bExact = (b.username === q || (b.name||'').toLowerCase() === q) ? 0 : 1;
            return aExact - bExact;
        })
        .map(g => ({
            type: 'group',
            id: g.id,
            username: g.username,
            name: g.name,
            avatar: g.avatar || null,
            memberCount: g.members.length,
            isMember: g.members.includes(viewer),
            isPrivate: !!g.isPrivate
        }));

    res.json({ results: [...users, ...groups] });
});

app.post('/api/block', (req, res) => {
    const { username, target } = req.body;
    const u = (username || '').toLowerCase(), t = (target || '').toLowerCase();
    if (!db.users[u] || !db.users[t] || u === t) return res.json({ success: false });
    if (!db.blocks[u]) db.blocks[u] = [];
    if (!db.blocks[u].includes(t)) db.blocks[u].push(t);
    saveDB();
    sendToUser(t, { type: 'chatlist' }); sendToUser(u, { type: 'chatlist' });
    sendToUser(u, { type: 'block_update', target: t, blocked: true });
    sendToUser(t, { type: 'block_update', target: u, blockedByOther: true });
    res.json({ success: true });
});
app.post('/api/unblock', (req, res) => {
    const { username, target } = req.body;
    const u = (username || '').toLowerCase(), t = (target || '').toLowerCase();
    if (db.blocks[u]) { db.blocks[u] = db.blocks[u].filter(x => x !== t); saveDB(); }
    sendToUser(t, { type: 'chatlist' }); sendToUser(u, { type: 'chatlist' });
    sendToUser(u, { type: 'block_update', target: t, blocked: false });
    sendToUser(t, { type: 'block_update', target: u, blockedByOther: false });
    res.json({ success: true });
});
app.get('/api/blocks/:username', (req, res) => {
    const u = req.params.username.toLowerCase();
    res.json({ list: db.blocks[u] || [] });
});

app.post('/api/upload', upload.single('file'), (req, res) => {
    if (!req.file) return res.json({ success: false, msg: 'File tidak ditemukan' });
    res.json({ success: true, file: {
        url: '/uploads/' + req.file.filename, name: req.file.originalname,
        size: req.file.size, mime: req.file.mimetype,
        uploadedAt: Date.now(), expiresAt: Date.now() + FILE_TTL_MS
    }});
});

app.get('/api/chat/:u1/:u2', (req, res) => {
    const u1 = req.params.u1.toLowerCase(), u2 = req.params.u2.toLowerCase();
    const cid = getChatId(u1, u2);
    if (db.unread[u1] && db.unread[u1][u2]) { db.unread[u1][u2] = 0; saveDB(); }
    const msgs = (db.chats[cid] || []).filter(m => !(m.deletedFor || []).includes(u1));
    res.json({ messages: msgs });
});
app.get('/api/groupchat/:groupId/:username', (req, res) => {
    const gid = req.params.groupId, u = req.params.username.toLowerCase();
    const g = db.groups[gid];
    if (!g || !g.members.includes(u)) return res.json({ messages: [] });
    const cid = groupChatId(gid);
    if (db.unread[u] && db.unread[u][cid]) { db.unread[u][cid] = 0; saveDB(); }
    const msgs = (db.chats[cid] || []).filter(m => !(m.deletedFor || []).includes(u));
    res.json({ messages: msgs });
});

app.get('/api/chats/:username', (req, res) => {
    const user = req.params.username.toLowerCase();
    const list = [];
    const seenGroups = new Set();
    const myBlocks = db.blocks[user] || [];

    Object.keys(db.chats).forEach(cid => {
        const msgs = db.chats[cid];
        if (!msgs || !msgs.length) return;
        const visible = msgs.filter(m => !(m.deletedFor || []).includes(user));
        if (!visible.length) return;
        const lastMsg = visible[visible.length - 1];

        if (cid.startsWith('grp_')) {
            const gid = cid.slice(4), g = db.groups[gid];
            if (!g || !g.members.includes(user)) return;
            seenGroups.add(gid);
            const unread = (db.unread[user] && db.unread[user][cid]) || 0;
            list.push({
                partner: gid, isGroup: true, name: g.name,
                avatar: g.avatar || null, username: g.username || null,
                isPrivate: !!g.isPrivate,
                lastMsg, unread, createdAt: g.createdAt
            });
        } else {
            const parts = cid.split('_');
            if (!parts.includes(user)) return;
            const partner = parts.find(u => u !== user);
            if (!partner || !db.users[partner]) return;
            const iBlocked = myBlocks.includes(partner);
            const theyBlocked = (db.blocks[partner] || []).includes(user);
            let avatar = db.users[partner].avatar || null;
            if (iBlocked || theyBlocked) avatar = null;
            const unread = (db.unread[user] && db.unread[user][partner]) || 0;
            const savedAs = getSavedName(user, partner);
            const savedByMe = isSavedBy(user, partner);
            const savedByThem = isSavedBy(partner, user);
            const introDismissed = (db.users[user].introDismissed || []).includes(partner);
            const displayName = getDisplayNameFor(user, partner);
            list.push({
                partner,
                isGroup: false,
                name: displayName,
                rawName: partner,
                savedAs: savedAs || null,
                savedByMe, savedByThem, introDismissed,
                avatar, lastMsg, unread,
                blocked: iBlocked || theyBlocked,
                isOnline: isUserOnline(partner)
            });
        }
    });

    Object.values(db.groups).forEach(g => {
        if (seenGroups.has(g.id)) return;
        if (!g.members.includes(user)) return;
        list.push({
            partner: g.id, isGroup: true, name: g.name,
            avatar: g.avatar || null, username: g.username || null,
            isPrivate: !!g.isPrivate,
            lastMsg: null, unread: 0, createdAt: g.createdAt
        });
    });

    list.sort((a, b) => {
        const ta = a.lastMsg?.timestamp || '';
        const tb = b.lastMsg?.timestamp || '';
        if (ta && tb) return tb.localeCompare(ta);
        if (ta && !tb) return -1;
        if (!ta && tb) return 1;
        return (b.createdAt || 0) - (a.createdAt || 0);
    });

    res.json(list);
});

app.post('/api/chat/delete', (req, res) => {
    const { username, chatId, forEveryone } = req.body;
    const u = (username || '').toLowerCase();
    if (forEveryone) {
        const msgs = db.chats[chatId] || [];
        const allMine = msgs.every(m => m.from === u);
        if (!allMine) return res.json({ success: false, msg: 'Tidak bisa hapus untuk semua: ada pesan dari orang lain' });
        delete db.chats[chatId]; saveDB();
        if (chatId.startsWith('grp_')) broadcastToGroup(chatId.slice(4), { type: 'chat_deleted', chatId, forEveryone: true });
        else chatId.split('_').forEach(p => sendToUser(p, { type: 'chat_deleted', chatId, forEveryone: true }));
    } else {
        const msgs = db.chats[chatId] || [];
        msgs.forEach(m => {
            if (!m.deletedFor) m.deletedFor = [];
            if (!m.deletedFor.includes(u)) m.deletedFor.push(u);
        });
        if (db.unread[u] && db.unread[u][chatId]) delete db.unread[u][chatId];
        saveDB();
        sendToUser(u, { type: 'chat_deleted', chatId, forMe: true });
    }
    res.json({ success: true });
});

function sanitizeGroup(g) {
    return {
        id: g.id, name: g.name, username: g.username || null,
        avatar: g.avatar || null, description: g.description || '',
        isPrivate: !!g.isPrivate,
        owner: g.owner, admins: g.admins,
        members: g.members.map(m => ({
            username: m,
            displayName: db.users[m]?.displayName || '',
            bio: db.users[m]?.bio || '',
            avatar: db.users[m]?.avatar || null
        })),
        inviteCode: g.inviteCode, createdAt: g.createdAt
    };
}

app.get('/api/groups/:username', (req, res) => {
    const u = req.params.username.toLowerCase();
    res.json(Object.values(db.groups).filter(g => g.members.includes(u)).map(g => ({
        id: g.id, name: g.name, username: g.username || null, avatar: g.avatar || null,
        owner: g.owner, admins: g.admins, memberCount: g.members.length,
        description: g.description || '', inviteCode: g.inviteCode, isPrivate: !!g.isPrivate
    })));
});
app.get('/api/group/:groupId', (req, res) => {
    const g = db.groups[req.params.groupId];
    if (!g) return res.json({ exists: false });
    res.json({ exists: true, group: sanitizeGroup(g) });
});
app.get('/api/group-by-username/:gusername', (req, res) => {
    const gu = req.params.gusername.toLowerCase();
    const viewer = (req.query.viewer || '').toLowerCase();
    const g = Object.values(db.groups).find(x => x.username === gu);
    if (!g) return res.json({ exists: false });
    if (g.isPrivate && !g.members.includes(viewer)) return res.json({ exists: false, private: true });
    res.json({ exists: true, group: sanitizeGroup(g), isMember: g.members.includes(viewer) });
});

app.post('/api/group/create', (req, res) => {
    const { username, name, groupUsername, members, description, isPrivate } = req.body;
    const u = (username || '').toLowerCase();
    if (!db.users[u]) return res.json({ success: false, msg: 'User tidak valid' });
    if (!name || !name.trim()) return res.json({ success: false, msg: 'Nama grup wajib diisi' });

    const gu = (groupUsername || '').trim().toLowerCase();
    if (!gu) return res.json({ success: false, msg: 'Username grup wajib diisi' });
    if (!/^[a-z0-9_.-]{3,20}$/.test(gu)) return res.json({ success: false, msg: 'Username grup 3-20 karakter' });
    if (usernameTaken(gu)) return res.json({ success: false, msg: 'Username grup sudah dipakai' });

    const memberList = Array.from(new Set([u, ...(members || []).map(x => String(x).toLowerCase())])).filter(m => db.users[m]);
    const gid = uid(10);
    const group = {
        id: gid,
        name: name.trim().slice(0, 60),
        username: gu,
        description: (description || '').slice(0, 200),
        isPrivate: !!isPrivate,
        avatar: null,
        owner: u,
        admins: [],
        members: memberList,
        inviteCode: uid(8),
        createdAt: Date.now()
    };
    db.groups[gid] = group; saveDB();
    memberList.forEach(m => {
        sendToUser(m, { type: 'chatlist' });
        if (m !== u) sendToUser(m, { type: 'group_added', group: sanitizeGroup(group) });
    });
    res.json({ success: true, group: sanitizeGroup(group) });
});

app.post('/api/group/update', (req, res) => {
    const { username, groupId, name, description, avatar, isPrivate, groupUsername } = req.body;
    const u = (username || '').toLowerCase(), g = db.groups[groupId];
    if (!g) return res.json({ success: false, msg: 'Grup tidak ditemukan' });
    if (!g.members.includes(u)) return res.json({ success: false, msg: 'Bukan member' });
    if (g.owner !== u && !g.admins.includes(u)) return res.json({ success: false, msg: 'Hanya admin yang bisa ubah info grup' });

    if (typeof name === 'string' && name.trim()) g.name = name.trim().slice(0, 60);
    if (typeof description === 'string') g.description = description.slice(0, 200);
    if (avatar !== undefined) g.avatar = avatar;
    if (typeof isPrivate === 'boolean') g.isPrivate = isPrivate;

    if (typeof groupUsername === 'string') {
        const gu = groupUsername.trim().toLowerCase();
        if (!gu) return res.json({ success: false, msg: 'Username grup wajib diisi' });
        if (!/^[a-z0-9_.-]{3,20}$/.test(gu)) return res.json({ success: false, msg: 'Username grup 3-20 karakter' });
        if (gu !== g.username) {
            if (usernameTaken(gu, g.id)) return res.json({ success: false, msg: 'Username grup sudah dipakai' });
            g.username = gu;
        }
    }

    saveDB();
    broadcastToGroup(g.id, { type: 'group_updated', group: sanitizeGroup(g) });
    Object.keys(db.users).forEach(uu => sendToUser(uu, { type: 'chatlist' }));
    res.json({ success: true, group: sanitizeGroup(g) });
});

app.post('/api/group/reset-invite', (req, res) => {
    const { username, groupId } = req.body;
    const u = (username || '').toLowerCase(), g = db.groups[groupId];
    if (!g) return res.json({ success: false, msg: 'Grup tidak ditemukan' });
    if (g.owner !== u && !g.admins.includes(u)) return res.json({ success: false, msg: 'Hanya pemilik / admin yang bisa reset tautan' });
    g.inviteCode = uid(8); saveDB();
    broadcastToGroup(g.id, { type: 'group_updated', group: sanitizeGroup(g) });
    res.json({ success: true, inviteCode: g.inviteCode });
});

app.post('/api/group/add-member', (req, res) => {
    const { username, groupId, member } = req.body;
    const u = (username || '').toLowerCase(), m = (member || '').toLowerCase(), g = db.groups[groupId];
    if (!g) return res.json({ success: false, msg: 'Grup tidak ditemukan' });
    if (!g.members.includes(u)) return res.json({ success: false });
    if (!db.users[m]) return res.json({ success: false, msg: 'User tidak ditemukan' });
    if (g.members.includes(m)) return res.json({ success: false, msg: 'Sudah jadi member' });
    g.members.push(m); saveDB();
    sendToUser(m, { type: 'chatlist' });
    sendToUser(m, { type: 'group_added', group: sanitizeGroup(g) });
    broadcastToGroup(g.id, { type: 'group_updated', group: sanitizeGroup(g) });
    res.json({ success: true });
});

app.post('/api/group/join-via-link', (req, res) => {
    const { username, inviteCode } = req.body;
    const u = (username || '').toLowerCase();
    if (!db.users[u]) return res.json({ success: false, msg: 'Login dulu' });
    const g = Object.values(db.groups).find(x => x.inviteCode === inviteCode);
    if (!g) return res.json({ success: false, msg: 'Link tidak valid / sudah kadaluarsa' });
    if (g.members.includes(u)) return res.json({ success: true, group: sanitizeGroup(g), already: true });
    g.members.push(u); saveDB();
    broadcastToGroup(g.id, { type: 'group_updated', group: sanitizeGroup(g) });
    sendToUser(u, { type: 'group_added', group: sanitizeGroup(g) });
    res.json({ success: true, group: sanitizeGroup(g) });
});

app.post('/api/group/join-public', (req, res) => {
    const { username, groupUsername } = req.body;
    const u = (username || '').toLowerCase();
    const gu = (groupUsername || '').trim().toLowerCase();
    if (!db.users[u]) return res.json({ success: false, msg: 'Login dulu' });
    const g = Object.values(db.groups).find(x => x.username === gu);
    if (!g) return res.json({ success: false, msg: 'Grup tidak ditemukan' });
    if (g.isPrivate) return res.json({ success: false, msg: 'Grup privat — butuh kode undangan' });
    if (g.members.includes(u)) return res.json({ success: true, group: sanitizeGroup(g), already: true });
    g.members.push(u); saveDB();
    broadcastToGroup(g.id, { type: 'group_updated', group: sanitizeGroup(g) });
    sendToUser(u, { type: 'group_added', group: sanitizeGroup(g) });
    res.json({ success: true, group: sanitizeGroup(g) });
});

app.post('/api/group/kick', (req, res) => {
    const { username, groupId, member } = req.body;
    const u = (username || '').toLowerCase(), m = (member || '').toLowerCase(), g = db.groups[groupId];
    if (!g) return res.json({ success: false });
    if (m === g.owner) return res.json({ success: false, msg: 'Tidak bisa kick pemilik grup' });
    const isOwner = g.owner === u, isAdmin = g.admins.includes(u);
    if (!isOwner && !isAdmin) return res.json({ success: false, msg: 'Bukan admin' });
    if (!isOwner && g.admins.includes(m)) return res.json({ success: false, msg: 'Admin tidak bisa kick admin lain' });
    g.members = g.members.filter(x => x !== m);
    g.admins = g.admins.filter(x => x !== m);
    saveDB();
    sendToUser(m, { type: 'group_kicked', groupId: g.id });
    sendToUser(m, { type: 'chatlist' });
    broadcastToGroup(g.id, { type: 'group_updated', group: sanitizeGroup(g) });
    res.json({ success: true });
});

app.post('/api/group/promote', (req, res) => {
    const { username, groupId, member, action } = req.body;
    const u = (username || '').toLowerCase(), m = (member || '').toLowerCase(), g = db.groups[groupId];
    if (!g) return res.json({ success: false });
    if (m === g.owner) return res.json({ success: false, msg: 'Pemilik tidak bisa diubah' });
    const isOwner = g.owner === u, isAdmin = g.admins.includes(u);
    if (!isOwner && !isAdmin) return res.json({ success: false, msg: 'Bukan admin' });
    if (action === 'promote') { if (!g.members.includes(m)) return res.json({ success: false }); if (!g.admins.includes(m)) g.admins.push(m); }
    else g.admins = g.admins.filter(x => x !== m);
    saveDB();
    broadcastToGroup(g.id, { type: 'group_updated', group: sanitizeGroup(g) });
    res.json({ success: true });
});

app.post('/api/group/delete', (req, res) => {
    const { username, groupId } = req.body;
    const u = (username || '').toLowerCase(), g = db.groups[groupId];
    if (!g) return res.json({ success: false });
    if (g.owner !== u) return res.json({ success: false, msg: 'Hanya pemilik yang bisa hapus grup' });
    const members = g.members.slice();
    delete db.groups[groupId]; delete db.chats[groupChatId(groupId)]; saveDB();
    members.forEach(m => { sendToUser(m, { type: 'group_deleted', groupId }); sendToUser(m, { type: 'chatlist' }); });
    res.json({ success: true });
});

app.post('/api/group/leave', (req, res) => {
    const { username, groupId } = req.body;
    const u = (username || '').toLowerCase(), g = db.groups[groupId];
    if (!g) return res.json({ success: false });
    if (g.owner === u) return res.json({ success: false, msg: 'Pemilik tidak bisa keluar, hapus grup' });
    g.members = g.members.filter(x => x !== u);
    g.admins = g.admins.filter(x => x !== u);
    saveDB();
    sendToUser(u, { type: 'chatlist' });
    broadcastToGroup(g.id, { type: 'group_updated', group: sanitizeGroup(g) });
    res.json({ success: true });
});

app.post('/api/message/delete', (req, res) => {
    const { username, chatId, messageId, forEveryone } = req.body;
    const u = (username || '').toLowerCase();
    const msgs = db.chats[chatId];
    if (!msgs) return res.json({ success: false });
    const idx = msgs.findIndex(m => m.id === messageId);
    if (idx === -1) return res.json({ success: false });
    const m = msgs[idx];
    if (forEveryone) {
        if (m.from !== u) return res.json({ success: false, msg: 'Hanya bisa hapus untuk semua pesan milik sendiri' });
        const afterCount = msgs.slice(idx + 1).filter(x => !x.deletedForEveryone).length;
        if (afterCount > 5) return res.json({ success: false, msg: 'Sudah terlalu lama. Hanya bisa hapus untuk saya.' });
        m.deletedForEveryone = true; m.text = ''; m.file = null;
        if (chatId.startsWith('grp_')) broadcastToGroup(chatId.slice(4), { type: 'message_deleted', chatId, messageId, forEveryone: true });
        else chatId.split('_').forEach(p => sendToUser(p, { type: 'message_deleted', chatId, messageId, forEveryone: true }));
    } else {
        if (!m.deletedFor) m.deletedFor = [];
        if (!m.deletedFor.includes(u)) m.deletedFor.push(u);
        sendToUser(u, { type: 'message_deleted', chatId, messageId, forMe: true });
    }
    saveDB();
    res.json({ success: true });
});

app.post('/api/status/create', (req, res) => {
    const { username, text, image, video } = req.body;
    const u = (username || '').toLowerCase();
    if (!db.users[u]) return res.json({ success: false });
    if (!text && !image && !video) return res.json({ success: false, msg: 'Isi teks, gambar, atau video' });
    const s = {
        id: uid(10),
        text: (text || '').slice(0, 500),
        image: image || null,
        video: video || null,
        createdAt: Date.now(),
        expiresAt: Date.now() + STATUS_TTL_MS,
        views: []
    };
    if (!db.statuses[u]) db.statuses[u] = [];
    db.statuses[u].push(s); saveDB();
    res.json({ success: true, status: s });
});
app.get('/api/status/list/:username', (req, res) => {
    purgeExpiredStatuses();
    const u = req.params.username.toLowerCase();
    if (!db.users[u]) return res.json({ statuses: [] });
    const now = Date.now();
    const list = [];
    Object.keys(db.statuses).forEach(owner => {
        if (owner === u) return;
        if ((db.blocks[u] || []).includes(owner)) return;
        if ((db.blocks[owner] || []).includes(u)) return;
        if (!isMutualSave(u, owner)) return;
        const arr = (db.statuses[owner] || []).filter(s => s.expiresAt > now);
        if (!arr.length) return;
        const latest = arr[arr.length - 1];
        const allViewed = arr.every(s => (s.views || []).includes(u));
        list.push({
            owner,
            displayName: getDisplayNameFor(u, owner),
            avatar: db.users[owner].avatar || null,
            count: arr.length, latestAt: latest.createdAt, allViewed
        });
    });
    list.sort((a, b) => b.latestAt - a.latestAt);
    res.json({ statuses: list });
});
app.get('/api/status/mine/:username', (req, res) => {
    purgeExpiredStatuses();
    const u = req.params.username.toLowerCase();
    const now = Date.now();
    const arr = (db.statuses[u] || []).filter(s => s.expiresAt > now).map(s => ({
        id: s.id, text: s.text, image: s.image, video: s.video,
        createdAt: s.createdAt, expiresAt: s.expiresAt,
        viewCount: (s.views || []).length
    }));
    res.json({ statuses: arr });
});
app.get('/api/status/view/:owner', (req, res) => {
    purgeExpiredStatuses();
    const owner = req.params.owner.toLowerCase();
    const viewer = (req.query.viewer || '').toLowerCase();
    if (viewer && viewer !== owner && !isMutualSave(viewer, owner)) {
        return res.json({ statuses: [], notMutual: true });
    }
    const now = Date.now();
    const arr = (db.statuses[owner] || []).filter(s => s.expiresAt > now);
    if (!arr.length) return res.json({ statuses: [] });
    arr.forEach(s => {
        if (!s.views) s.views = [];
        if (viewer && !s.views.includes(viewer)) s.views.push(viewer);
    });
    saveDB();
    const ownerInfo = db.users[owner] || {};
    res.json({
        owner,
        displayName: viewer ? getDisplayNameFor(viewer, owner) : (ownerInfo.displayName || ''),
        avatar: ownerInfo.avatar || null,
        statuses: arr.map(s => ({
            id: s.id, text: s.text, image: s.image, video: s.video,
            createdAt: s.createdAt, viewCount: (s.views || []).length
        }))
    });
});
app.post('/api/status/delete', (req, res) => {
    const { username, statusId } = req.body;
    const u = (username || '').toLowerCase();
    if (!db.statuses[u]) return res.json({ success: false });
    db.statuses[u] = db.statuses[u].filter(s => s.id !== statusId);
    saveDB();
    res.json({ success: true });
});

const onlineClients = {};
const viewing = {};
const activeCalls = {};
const callTimeouts = {};

function sendToUser(username, payload) {
    const c = onlineClients[username];
    if (c && c.readyState === WebSocket.OPEN) {
        try { c.send(JSON.stringify(payload)); return true; } catch (e) {}
    }
    return false;
}
function broadcastToGroup(groupId, payload) {
    const g = db.groups[groupId];
    if (!g) return;
    g.members.forEach(m => sendToUser(m, payload));
}
function broadcastStatus(username, status) {
    Object.keys(onlineClients).forEach(other => {
        if (other === username) return;
        sendToUser(other, {
            type: 'status',
            user: username,
            status,
            displayName: displayOf(username),
            lastSeen: status === 'offline' ? (db.users[username]?.lastSeen || Date.now()) : null
        });
    });
}
function isBlockedBetween(a, b) {
    return (db.blocks[a] || []).includes(b) || (db.blocks[b] || []).includes(a);
}
function markMessagesRead(readerUser, chatId) {
    const msgs = db.chats[chatId];
    if (!msgs) return;
    const newlyRead = [];
    msgs.forEach(m => {
        if (m.from === readerUser) return;
        if (m.deletedForEveryone) return;
        if (!m.readBy) m.readBy = [];
        if (m.readBy.includes(readerUser)) return;
        m.readBy.push(readerUser);
        newlyRead.push({ id: m.id, from: m.from });
    });
    if (newlyRead.length) {
        saveDB();
        const bySender = {};
        newlyRead.forEach(r => { if (!bySender[r.from]) bySender[r.from] = []; bySender[r.from].push(r.id); });
        Object.entries(bySender).forEach(([sender, ids]) => {
            sendToUser(sender, { type: 'status', status: 'read', ids, chatId });
        });
    }
}

function clearCallTimeout(user) {
    if (callTimeouts[user]) { clearTimeout(callTimeouts[user]); delete callTimeouts[user]; }
}
function endCallBetween(a, b, reason) {
    clearCallTimeout(a); clearCallTimeout(b);
    delete activeCalls[a]; delete activeCalls[b];
    if (a) sendToUser(a, { type: 'call-hangup', from: b, reason });
    if (b) sendToUser(b, { type: 'call-hangup', from: a, reason });
}

wss.on('connection', (ws) => {
    let currentUser = null;
    ws.on('message', (raw) => {
        let data;
        try { data = JSON.parse(raw); } catch { return; }
        if (data.type === 'auth') {
            currentUser = (data.username || '').trim().toLowerCase();
            if (!db.users[currentUser]) return;
            onlineClients[currentUser] = ws;
            sendToUser(currentUser, { type: 'chatlist' });
            broadcastStatus(currentUser, 'online');
            console.log('[WS] user online:', currentUser);
            return;
        }
        if (!currentUser) return;
        if (data.type === 'viewing') {
            const prev = viewing[currentUser];
            viewing[currentUser] = data.partner ? String(data.partner).toLowerCase() : null;
            if (viewing[currentUser] && viewing[currentUser] !== prev) {
                const cid = viewing[currentUser].startsWith('grp_') ? viewing[currentUser] : getChatId(currentUser, viewing[currentUser]);
                markMessagesRead(currentUser, cid);
            }
            return;
        }

        if (data.type === 'call-offer') {
            const target = String(data.to || '').toLowerCase();
            console.log('[SERVER CALL] offer from', currentUser, '→', target, '| type:', data.callType);
            if (!db.users[target]) return;
            if (activeCalls[target]) { sendToUser(currentUser, { type: 'call-busy', by: target }); return; }
            if (activeCalls[currentUser]) { sendToUser(currentUser, { type: 'call-busy-self' }); return; }
            activeCalls[currentUser] = { peer: target, type: data.callType || 'audio', startedAt: Date.now(), status: 'ringing' };
            activeCalls[target] = { peer: currentUser, type: data.callType || 'audio', startedAt: Date.now(), status: 'ringing' };
            const ok = sendToUser(target, {
                type: 'call-offer',
                from: currentUser,
                fromName: displayOf(currentUser),
                fromAvatar: db.users[currentUser]?.avatar || null,
                callType: data.callType || 'audio',
                sdp: data.sdp
            });
            console.log('[SERVER CALL] offer forwarded:', ok);
            if (!ok) {
                delete activeCalls[currentUser];
                delete activeCalls[target];
                sendToUser(currentUser, { type: 'call-unavailable', by: target });
                return;
            }
            clearCallTimeout(currentUser);
            callTimeouts[currentUser] = setTimeout(() => {
                if (activeCalls[currentUser] && activeCalls[currentUser].peer === target && activeCalls[currentUser].status === 'ringing') {
                    endCallBetween(currentUser, target, 'timeout');
                }
            }, CALL_TIMEOUT_MS);
            return;
        }

        if (data.type === 'call-answer') {
            const target = String(data.to || '').toLowerCase();
            console.log('[SERVER CALL] answer from', currentUser, '→', target, '| active calls:', Object.keys(activeCalls));
            if (!db.users[target]) {
                console.warn('[SERVER CALL] target user not found:', target);
                return;
            }
            if (activeCalls[currentUser]) activeCalls[currentUser].status = 'active';
            if (activeCalls[target]) activeCalls[target].status = 'active';
            clearCallTimeout(currentUser); clearCallTimeout(target);
            const ok = sendToUser(target, { type: 'call-answer', from: currentUser, sdp: data.sdp });
            console.log('[SERVER CALL] answer forwarded:', ok);
            return;
        }

        if (data.type === 'call-ice') {
            const target = String(data.to || '').toLowerCase();
            sendToUser(target, { type: 'call-ice', from: currentUser, candidate: data.candidate });
            return;
        }

        if (data.type === 'call-hangup' || data.type === 'call-reject') {
            const target = String(data.to || '').toLowerCase();
            console.log('[SERVER CALL]', data.type, 'from', currentUser, '→', target);
            clearCallTimeout(currentUser); clearCallTimeout(target);
            delete activeCalls[currentUser];
            delete activeCalls[target];
            sendToUser(target, { type: data.type, from: currentUser, reason: data.reason || null });
            return;
        }

        if (data.type === 'message') {
            const from = currentUser;
            const isGroup = !!data.isGroup;
            const to = String(data.to || '').trim();
            const buildPayload = (cid) => {
                const p = {
                    id: data.id || (Date.now().toString(36) + uid(4)),
                    from,
                    fromName: displayOf(from),
                    to: isGroup ? to : to.toLowerCase(),
                    isGroup, chatId: cid,
                    msgType: data.msgType || 'text', text: data.text || '',
                    timestamp: nowTime(), readBy: []
                };
                if (data.replyTo) {
                    p.replyTo = { ...data.replyTo };
                    if (p.replyTo.from) p.replyTo.fromName = displayOf(p.replyTo.from);
                }
                if (data.forwarded) p.forwarded = true;
                if (data.file) {
                    p.file = {
                        name: data.file.name, size: data.file.size, mime: data.file.mime,
                        url: data.file.url, duration: data.file.duration || null,
                        uploadedAt: data.file.uploadedAt || Date.now(),
                        expiresAt: data.file.expiresAt || (Date.now() + FILE_TTL_MS)
                    };
                }
                return p;
            };
            if (isGroup) {
                const g = db.groups[to];
                if (!g || !g.members.includes(from)) return;
                const cid = groupChatId(to);
                const payload = buildPayload(cid);
                g.members.forEach(m => {
                    if (m === from) return;
                    if (viewing[m] === cid) payload.readBy.push(m);
                    else { if (!db.unread[m]) db.unread[m] = {}; db.unread[m][cid] = (db.unread[m][cid] || 0) + 1; }
                });
                if (!db.chats[cid]) db.chats[cid] = [];
                db.chats[cid].push(payload); saveDB();
                g.members.forEach(m => sendToUser(m, payload));
                g.members.forEach(m => sendToUser(m, { type: 'chatlist' }));
                if (payload.readBy.length > 0) sendToUser(from, { type: 'status', status: 'read', ids: [payload.id], chatId: cid });
                return;
            }
            const targetUser = to.toLowerCase();
            if (!db.users[targetUser] || targetUser === from) return;
            if (isBlockedBetween(from, targetUser)) { sendToUser(from, { type: 'blocked_error', messageId: data.id }); return; }
            const cid = getChatId(from, targetUser);
            const payload = buildPayload(cid);
            if (viewing[targetUser] === from) {
                payload.readBy.push(targetUser);
                if (!db.unread[targetUser]) db.unread[targetUser] = {};
                db.unread[targetUser][from] = 0;
            } else {
                if (!db.unread[targetUser]) db.unread[targetUser] = {};
                db.unread[targetUser][from] = (db.unread[targetUser][from] || 0) + 1;
            }
            if (!db.chats[cid]) db.chats[cid] = [];
            db.chats[cid].push(payload); saveDB();
            const delivered = sendToUser(targetUser, payload);
            sendToUser(from, payload);
            sendToUser(from, { type: 'status', status: 'delivered', id: payload.id });
            if (payload.readBy.includes(targetUser)) sendToUser(from, { type: 'status', status: 'read', ids: [payload.id], chatId: cid });
            sendToUser(from, { type: 'chatlist' });
            if (delivered) sendToUser(targetUser, { type: 'chatlist' });
            return;
        }
    });
    ws.on('close', () => {
        if (currentUser && onlineClients[currentUser] === ws) {
            delete onlineClients[currentUser];
            delete viewing[currentUser];
            if (db.users[currentUser]) {
                db.users[currentUser].lastSeen = Date.now();
                saveDB();
            }
            if (activeCalls[currentUser]) {
                const peer = activeCalls[currentUser].peer;
                clearCallTimeout(currentUser); clearCallTimeout(peer);
                delete activeCalls[currentUser];
                if (peer && activeCalls[peer] && activeCalls[peer].peer === currentUser) {
                    delete activeCalls[peer];
                    sendToUser(peer, { type: 'call-hangup', from: currentUser, reason: 'disconnected' });
                }
            }
            broadcastStatus(currentUser, 'offline');
            console.log('[WS] user offline:', currentUser);
        }
    });
});

const PORT = process.env.PORT || 3000;
const HOST = process.env.HOST || '0.0.0.0';
server.listen(PORT, HOST, () => {
    console.log(`NexChat server aktif di http://${HOST}:${PORT}`);
    console.log(`DATA_DIR: ${DATA_DIR}`);
});
process.on('SIGTERM', () => {
    console.log('SIGTERM, menutup…');
    try { saveDB(); } catch {}
    server.close(() => process.exit(0));
    setTimeout(() => process.exit(0), 5000);
});
process.on('SIGINT', () => {
    try { saveDB(); } catch {}
    server.close(() => process.exit(0));
});

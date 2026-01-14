# Remote Control - Quick Start Guide

## 🚀 Testing the Feature (5 minutes)

### Step 1: Clear Environment & Authenticate

```bash
# Clear any staging configuration
unset PDD_CLOUD_URL
unset NEXT_PUBLIC_FIREBASE_API_KEY

# Clear old auth
rm -f ~/.pdd/jwt_cache

# Authenticate (will open browser)
pdd auth login
```

✅ You should see: "Authentication successful!"

### Step 2: Start a Remote Session

**Terminal 1:**
```bash
cd ~/Desktop/PDD_PRIVATE/pdd-main  # or any project
pdd connect
```

✅ Expected output:
```
✓ Session registered with PDD Cloud
  Session ID: abc-123-def-456-...
  Cloud URL: https://prompt-driven-development.web.app/connect/abc-123...

Starting server on http://localhost:9876
✓ Server running
```

✅ Browser should open to `http://localhost:9876`

### Step 3: Control Remote Session from Local UI

**Terminal 2 (optional - for two-machine test):**
```bash
cd ~/another-project
pdd connect
```

**In Browser at http://localhost:9876:**

1. **Look at the header** (large screens only):
   - You should see "Remote Session" dropdown
   - And "Execution Mode" toggle

2. **Select Your Session:**
   - Click the "Remote Session" dropdown
   - Select the session (shows project name @ hostname)
   - Should show status badge: 🟢 Active

3. **Switch to Remote Mode:**
   - Click "Remote" button in the toggle
   - Should turn purple and show info message

4. **Run a Test Command:**
   - Go to "Prompts" tab
   - Create a simple prompt or use existing one
   - Click "Generate"

5. **Watch Execution:**
   - Toast notification: "Command submitted to remote session"
   - Job appears in dashboard with `[Remote]` prefix
   - Status updates every 5 seconds
   - Final notification when complete

## 🎯 What to Look For

### Success Indicators

✅ Remote session appears in dropdown
✅ Can toggle to "Remote" mode
✅ Command submission shows toast
✅ Job has `[Remote]` prefix in dashboard
✅ Status changes from "pending" → "processing" → "completed"
✅ Completion notification appears

### Common Issues

**Session doesn't appear:**
- Check `pdd auth status` - must be authenticated
- Verify session is running in other terminal
- Check browser console for API errors

**Can't toggle to Remote:**
- Must select a session first
- Session must be "active" (check status badge)

**Command doesn't execute:**
- Check remote terminal for "Found pending command" messages
- Verify session ID matches in both terminals

## 📱 Mobile/Small Screens

The remote controls are currently hidden on small screens (< lg breakpoint).

To test on smaller screens, temporarily edit `pdd/frontend/App.tsx`:

Change:
```tsx
<div className="hidden lg:flex items-center gap-3 ...">
```

To:
```tsx
<div className="flex items-center gap-3 ...">
```

## 🔍 Debugging

### Check Authentication

```bash
pdd auth status
# Should show: ✓ Authenticated with PDD Cloud

cat ~/.pdd/jwt_cache | python3 -m json.tool
# Should show valid JWT with future expires_at
```

### Check Session Registration

Look for this in terminal output:
```
✓ Session registered with PDD Cloud
  Session ID: 1234abcd-...
```

### Check Browser Console

Open DevTools → Console, look for:
```javascript
// Should see successful API calls
GET /api/v1/auth/jwt-token → 200
GET https://.../listSessions → 200 {sessions: [...]}
POST https://.../submitCommand → 201 {commandId: "..."}
```

### Check Firestore

Firebase Console → Firestore Database:
```
remote_sessions/
  {your-session-id}/
    commands/
      {command-id}/
        status: "pending" → "processing" → "completed"
```

## 🎉 Success Criteria

You've successfully tested the feature when:

- [x] Remote session appears in UI dropdown
- [x] Can switch between Local/Remote modes
- [x] Command submitted from local UI
- [x] Executes on remote machine
- [x] Results appear in local UI
- [x] Status updates in real-time

## 📚 More Information

- Full setup guide: `REMOTE_CONTROL_SETUP.md`
- Architecture details in the implementation plan
- Troubleshooting: See setup guide

## ⚡ One-Line Test

After authentication:
```bash
pdd connect  # Opens browser, registers session
# In browser: Select session → Toggle to Remote → Run command → Watch results!
```

That's it! You're now controlling remote PDD sessions from your local browser. 🚀

# Remote Session Control - Setup & Testing Guide

This guide walks you through setting up and testing the new **local UI remote control** feature for PDD.

## Overview

This feature enables your local PDD UI (running at `http://localhost:9876`) to discover and control remote PDD sessions running on other machines, using PDD Cloud as a secure message bus.

```
┌─────────────┐         ┌──────────────┐         ┌─────────────┐
│ Local UI    │────────▶│  PDD Cloud   │────────▶│ Remote      │
│ (Laptop)    │   JWT   │  (Staging)   │  Poll   │ Session     │
│ localhost   │◀────────│  Firestore   │◀────────│ (Server)    │
└─────────────┘ Results └──────────────┘ Updates └─────────────┘
```

## Prerequisites

- Two machines or terminals (can be same machine for testing)
- PDD installed on both
- GitHub account for authentication

## Setup Instructions

### 1. Configure Environment for Staging

**Option A: Temporary (for current terminal session)**
```bash
source setup_staging_env.sh
```

**Option B: Permanent (recommended)**

Add to your `~/.zshrc` or `~/.bashrc`:
```bash
# PDD Staging Environment
export PDD_CLOUD_URL="https://us-central1-prompt-driven-development-stg.cloudfunctions.net"
export NEXT_PUBLIC_FIREBASE_API_KEY="AIzaSyC7rX6OLGVDlzkU8q7nK_i14ggOqjNz2N4"
```

Then reload: `source ~/.zshrc`

### 2. Clear Old Authentication

If you previously used PDD with production:
```bash
rm -f ~/.pdd/jwt_cache
pdd auth logout
```

### 3. Authenticate with Staging

```bash
pdd auth login
```

This will:
1. Open GitHub in your browser
2. Ask you to authorize the PDD application
3. Cache a JWT token for staging Firebase

**Verify authentication:**
```bash
pdd auth status
```

Should show: `✓ Authenticated with PDD Cloud`

## Testing the Feature

### Test 1: Single Machine (Simplest)

**Terminal 1 - Remote Session:**
```bash
cd ~/test-project
pdd connect
```

Expected output:
```
✓ Session registered with PDD Cloud
  Session ID: abc123-def456-...
  Cloud URL: https://...

Starting server on http://localhost:9876
```

**Terminal 2 - Local Control:**
```bash
cd ~/another-project
pdd connect
```

Browser opens to `http://localhost:9876`

**In the Browser:**

1. **Check the header** (on large screens, you'll see):
   - "Remote Session" dropdown
   - "Execution Mode" toggle

2. **Select remote session:**
   - Click the dropdown
   - Should show: `test-project @ your-hostname`
   - Select it

3. **Toggle to Remote mode:**
   - Click "Remote" button
   - Should turn purple/highlighted

4. **Run a command:**
   - Go to "Prompts" tab
   - Select or create a prompt
   - Click "Generate"
   - Watch for toast: "Command submitted to remote session"

5. **Observe execution:**
   - Job appears in dashboard with `[Remote]` prefix
   - Status updates every 5 seconds
   - When complete: "Remote command completed successfully"

### Test 2: Two Machines

**Machine A (Server/Remote):**
```bash
ssh user@server-machine
cd ~/production-project
export PDD_CLOUD_URL="https://us-central1-prompt-driven-development-stg.cloudfunctions.net"
export NEXT_PUBLIC_FIREBASE_API_KEY="AIzaSyC7rX6OLGVDlzkU8q7nK_i14ggOqjNz2N4"
pdd auth login  # Authenticate
pdd connect     # Register and run session
```

**Machine B (Laptop/Local):**
```bash
cd ~/local-project
export PDD_CLOUD_URL="https://us-central1-prompt-driven-development-stg.cloudfunctions.net"
export NEXT_PUBLIC_FIREBASE_API_KEY="AIzaSyC7rX6OLGVDlzkU8q7nK_i14ggOqjNz2N4"
pdd auth login  # Same GitHub account!
pdd connect     # Open local UI
```

Open browser to `http://localhost:9876` and follow steps from Test 1.

Commands submitted from Machine B will execute on Machine A!

## Architecture Details

### Cloud Function: submitCommand

**Endpoint:** `https://us-central1-prompt-driven-development-stg.cloudfunctions.net/submitCommand`

**Request:**
```json
POST /submitCommand
Headers:
  Authorization: Bearer <JWT_TOKEN>
  Content-Type: application/json
Body:
{
  "sessionId": "abc123-def456-...",
  "type": "generate",
  "payload": {
    "args": {"prompt_file": "prompts/example.prompt"},
    "options": {"strength": 0.8, "force": true}
  }
}
```

**Response:**
```json
{
  "commandId": "cmd-xyz-...",
  "status": "pending",
  "sessionId": "abc123-...",
  "createdAt": "2026-01-13T16:00:00Z"
}
```

### Firestore Structure

```
remote_sessions/
  {sessionId}/
    - user_id: "firebase-user-id"
    - project_name: "test-project"
    - status: "active"
    - last_heartbeat: timestamp

    commands/
      {commandId}/
        - command_id: "cmd-xyz"
        - type: "generate"
        - status: "pending" | "processing" | "completed" | "failed"
        - payload: {...}
        - response: {...}
        - created_at: timestamp
```

### Polling Mechanism

**Remote Machine (Server):**
- Polls `getCommands` endpoint every 5 seconds
- Filters for `status=pending`
- Executes commands locally
- Updates status via `updateCommand`

**Local UI (Browser):**
- Polls `getRemoteCommandStatus` every 5 seconds after submission
- Updates job dashboard with status
- Shows completion notification
- Timeout after 10 minutes

## Troubleshooting

### Remote session doesn't appear in dropdown

**Check authentication:**
```bash
pdd auth status
```

**Check JWT token:**
```bash
cat ~/.pdd/jwt_cache | python3 -m json.tool
```

Should show staging audience:
```json
{
  "jwt": "eyJ...",
  "expires_at": 1234567890,
  "aud": "prompt-driven-development-stg"  // Should be -stg!
}
```

**Check Firestore:**
- Open Firebase Console
- Project: `prompt-driven-development-stg`
- Firestore Database → `remote_sessions`
- Verify your session exists with correct `user_id`

### "Authentication failed" error

You're using a production token with staging cloud:

```bash
rm -f ~/.pdd/jwt_cache
pdd auth logout
pdd auth login  # Re-authenticate
```

### Command doesn't execute

**Check remote machine logs:**
- Look for "Found 1 pending command(s)" messages
- Check for execution errors

**Check browser console:**
- Open DevTools → Console
- Look for API errors from `listRemoteSessions` or `submitRemoteCommand`

**Verify session status:**
- Session must be "active" (heartbeat within last 2 minutes)
- Check `last_heartbeat` timestamp in Firestore

### Server fails to start

**Missing dependencies:**
```bash
cd ~/Desktop/PDD_PRIVATE/pdd-main
pip install -e .
```

**Import errors:**
```bash
python -c "from pdd.server.app import create_app; print('OK')"
```

## Security Notes

- All endpoints require JWT authentication
- Session ownership verified before command submission
- Commands scoped to specific sessions (no cross-session access)
- Cloud acts only as message bus (doesn't execute code)
- Same authentication mechanism as existing PDD Cloud features

## Implementation Files

### Cloud Functions (pdd_cloud/)
- `backend/functions/submit_command.py` - New endpoint
- `backend/functions/main.py` - Routing added

### Local Client (pdd-main/)
- `pdd/server/routes/auth.py` - JWT token endpoint
- `pdd/frontend/api.ts` - API methods
- `pdd/frontend/components/RemoteSessionSelector.tsx` - UI component
- `pdd/frontend/components/ExecutionModeToggle.tsx` - UI component
- `pdd/frontend/App.tsx` - Integration logic

## Next Steps

Once testing is complete:

1. **Deploy to Production:**
   - Deploy `submitCommand` to production cloud functions
   - Update documentation for production URLs
   - Remove staging environment variables

2. **Enhance UI:**
   - Add mobile-responsive layout for remote controls
   - Show remote execution progress in real-time
   - Add session metadata (Python version, platform, etc.)

3. **Add Features:**
   - Multiple session selection (run on all)
   - Session groups/tags
   - Command history for remote sessions
   - File sync between local and remote

## Support

If you encounter issues:
1. Check this guide's troubleshooting section
2. Review browser console for errors
3. Check Firebase Console → Firestore for session data
4. Verify environment variables are set correctly

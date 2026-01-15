# Architecture Sync Example Project

This example project demonstrates the bidirectional sync functionality between `architecture.json` and prompt file metadata tags.

## Project Structure

```
example_project/
├── architecture.json          # Architecture file (with outdated info)
├── prompts/                    # Prompt files with metadata tags
│   ├── database_python.prompt
│   ├── user_service_python.prompt
│   └── api_server_python.prompt
└── README.md                   # This file
```

## What's Included

### Prompts with Metadata Tags

All prompt files include XML metadata tags:
- `<pdd-reason>`: Brief description of module's purpose
- `<pdd-interface>`: JSON interface specification with functions
- `<pdd-dependency>`: Dependencies on other prompts

### Outdated Architecture.json

The `architecture.json` file intentionally contains outdated information:
- Reason fields don't match the prompts
- Dependencies are incomplete or missing
- Interface information is outdated

This allows you to test the sync functionality and see how it updates the architecture from the prompt tags.

## Testing the Sync Functionality

### Prerequisites

1. Make sure the PDD server is running:
   ```bash
   cd /path/to/pdd-architecture-prompt-sync
   pdd serve
   ```

2. Open PDD Connect in your browser:
   ```
   http://localhost:8000
   ```

### Test Workflow

#### 1. Copy Example Project

Copy this example project to your working directory:
```bash
# From the pdd-architecture-prompt-sync directory
cp -r example_project ~/my_test_project
cd ~/my_test_project
```

#### 2. View Current Architecture

Open PDD Connect and navigate to the Architecture tab:
1. Load the architecture file: `architecture.json`
2. Observe the current (outdated) information in the graph

Note the outdated information:
- Reason fields say "outdated - will be updated by sync"
- Dependencies are incomplete
- Interfaces have minimal information

#### 3. Sync from Prompts (Frontend)

1. Click the **"Sync from Prompts"** button in the GraphToolbar (purple button)
2. Review the sync modal explanation
3. Click **"Sync Now"**
4. Wait for the sync to complete

Expected results:
- ✅ 3 modules updated
- ✅ Validation passed (no circular dependencies)
- ✅ Changes shown in details:
  - `reason` fields updated
  - `interface` fields populated/updated
  - `dependencies` arrays corrected

5. Close the modal and observe the updated architecture graph

#### 4. Verify Changes

Check the updated `architecture.json` file:
```bash
cat architecture.json
```

You should see:
- Reason fields match what's in the prompts
- Interface objects are fully populated
- Dependencies are correct:
  - `database_python.prompt`: no dependencies
  - `user_service_python.prompt`: depends on `database_python.prompt`
  - `api_server_python.prompt`: depends on both database and user_service

#### 5. Test Sync via API (Optional)

You can also test the sync endpoint directly via curl:
```bash
# Sync all prompts
curl -X POST http://localhost:8000/api/v1/architecture/sync-from-prompts \
  -H "Content-Type: application/json" \
  -d '{"filenames": null, "dry_run": false}' \
  | jq .

# Dry run (preview changes without applying)
curl -X POST http://localhost:8000/api/v1/architecture/sync-from-prompts \
  -H "Content-Type: application/json" \
  -d '{"dry_run": true}' \
  | jq .

# Sync specific prompt only
curl -X POST http://localhost:8000/api/v1/architecture/sync-from-prompts \
  -H "Content-Type: application/json" \
  -d '{"filenames": ["user_service_python.prompt"]}' \
  | jq .
```

#### 6. Test Reverse Direction (Architecture → Prompt)

Generate a new prompt file:
```bash
# This will inject tags from architecture.json
pdd generate new_module --output prompts/new_module_python.prompt
```

The generated prompt will automatically include metadata tags if an entry exists in architecture.json.

### 7. Edit Tags and Re-sync

Try editing the prompt files:

1. Open `prompts/user_service_python.prompt`
2. Modify the `<pdd-reason>` tag:
   ```xml
   <pdd-reason>Handles user auth, authorization, and profile updates</pdd-reason>
   ```
3. Add a new dependency:
   ```xml
   <pdd-dependency>email_service_python.prompt</pdd-dependency>
   ```
4. Save the file
5. Click "Sync from Prompts" again in PDD Connect
6. Verify the changes were applied to architecture.json

## Expected Sync Results

### Before Sync

**architecture.json:**
```json
{
  "reason": "User service (outdated - will be updated by sync)",
  "dependencies": [],
  "interface": {
    "type": "module",
    "module": {
      "functions": [
        {"name": "authenticate_user", "signature": "(username, password)", "returns": "User"}
      ]
    }
  }
}
```

### After Sync

**architecture.json:**
```json
{
  "reason": "Handles user authentication, authorization, and profile management",
  "dependencies": ["database_python.prompt"],
  "interface": {
    "type": "module",
    "module": {
      "functions": [
        {
          "name": "authenticate_user",
          "signature": "(username: str, password: str) -> Optional[User]",
          "returns": "Optional[User]",
          "sideEffects": ["Validates credentials"]
        },
        {
          "name": "create_user",
          "signature": "(username: str, email: str, password: str) -> User",
          "returns": "User",
          "sideEffects": ["Creates user in database"]
        },
        {
          "name": "get_user_by_id",
          "signature": "(user_id: int) -> Optional[User]",
          "returns": "Optional[User]",
          "sideEffects": ["None"]
        },
        {
          "name": "update_user_profile",
          "signature": "(user_id: int, profile_data: Dict) -> bool",
          "returns": "bool",
          "sideEffects": ["Updates user in database"]
        }
      ]
    }
  }
}
```

## Validation Tests

### Test Circular Dependency Detection

1. Edit `prompts/database_python.prompt` and add:
   ```xml
   <pdd-dependency>user_service_python.prompt</pdd-dependency>
   ```
2. This creates a cycle: database → user_service → database
3. Click "Sync from Prompts"
4. Expected result: ❌ Validation error: "Circular dependency detected"
5. The architecture.json should NOT be updated

### Test Missing Dependency Warning

1. Edit `prompts/user_service_python.prompt` and add:
   ```xml
   <pdd-dependency>nonexistent_python.prompt</pdd-dependency>
   ```
2. Click "Sync from Prompts"
3. Expected result: ⚠️ Warning about missing file (but sync proceeds)

## Advanced Features

### Lenient Validation

The sync is lenient - missing tags are OK:
- If a prompt has no `<pdd-reason>` tag, the reason field won't be updated
- If a prompt has no `<pdd-interface>` tag, the interface field won't be updated
- Partial updates are supported

### Prompts as Source of Truth

- Tags in prompts ALWAYS override what's in architecture.json
- Manual edits to tags in prompts are preserved
- architecture.json is the derived artifact, prompts are authoritative

### Field Preservation

Sync only updates fields that have tags:
- `description`, `priority`, `tags`, `filepath` are never modified by sync
- This allows you to maintain manual architecture.json metadata

## Migrating Existing Projects

If you have an existing project with prompts that don't have tags yet:

```bash
# Preview what would be added
python migrate_architecture_tags.py

# Apply tags to all prompts
python migrate_architecture_tags.py --apply

# Apply to specific prompts only
python migrate_architecture_tags.py --apply --filter "user_*"
```

This will read your architecture.json and inject metadata tags into your prompt files.

## Troubleshooting

### Sync Button Not Visible

- Make sure you're NOT in edit mode (the "Edit" button should not be highlighted)
- The sync button only appears in view mode

### Validation Errors

- Check for circular dependencies (A → B → A)
- Verify all dependency filenames end with `.prompt`
- Ensure JSON in `<pdd-interface>` tags is valid

### Tags Not Being Parsed

- Check that tags are properly closed (e.g., `</pdd-reason>`)
- Verify JSON in interface tags is valid
- Make sure tags are at the top of the prompt file (after any includes)

### Architecture Not Updating

- Check browser console for errors
- Verify the PDD server is running
- Check server logs for sync endpoint errors
- Try a dry run first to see what would change

## Next Steps

1. ✅ Test the sync functionality with this example project
2. ✅ Try editing prompt tags and re-syncing
3. ✅ Test validation (circular dependencies)
4. ✅ Migrate your own project prompts
5. ✅ Integrate sync into your workflow

For more information, see:
- `docs/prompting_guide.md` - Complete tag documentation
- `docs/examples/prompt_with_metadata.prompt` - Full example
- `test_bidirectional_sync.py` - Automated tests

## Summary

This example demonstrates:
- ✅ Prompt → Architecture sync (primary direction)
- ✅ Architecture → Prompt generation (reverse direction)
- ✅ Lenient validation (missing tags OK)
- ✅ Prompts as source of truth
- ✅ Validation integration (circular dependency detection)
- ✅ Field preservation (only synced fields updated)
- ✅ Frontend integration (Sync from Prompts button)

Happy syncing! 🎉

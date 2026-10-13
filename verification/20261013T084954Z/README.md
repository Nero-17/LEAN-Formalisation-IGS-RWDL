# Evidence for this snapshot

`integration-545.json` is the last completed common-dependency batch. Only its `verified_source_files` are asserted to match its snapshot; other historical snapshot entries need not be current.

`accepted-receipts.json` contains independently accepted whole-file results and relative paths to their unchanged logs. `source-status.json` records every current project Lean source and explicitly identifies sources not covered by these receipts. `verified-targets.txt` is the union of selected shared targets and accepted later targets.

Logs are original compiler evidence; paths in their diagnostics are historical machine paths. No dependency caches, credentials, or compiled binaries are required to inspect the manifests.

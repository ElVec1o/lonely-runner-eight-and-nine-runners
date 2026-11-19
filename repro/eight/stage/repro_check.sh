#!/bin/bash
# repro_check.sh P ... : regenerate the staged sources of prime(s) P and compare every file with ../E8STAGE.tsv (no Lean).  Same as regen_e8stage.sh.
# (The development tree compared the combined sha256 of the ORIGINAL sources with records/P<p>/record.txt; the shipped generator differs from the original in
# line 1 of every generated file, so the comparison here is per file against E8STAGE.tsv; see ../README.md.)
exec bash "$(dirname "$0")/regen_e8stage.sh" "$@"

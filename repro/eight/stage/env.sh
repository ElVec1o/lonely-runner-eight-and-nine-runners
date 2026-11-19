# Sourced by the stage scripts (repro/eight/stage). All paths are relative to the repository root.
S=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)          # repro/eight/stage
E=$(cd "$S/.." && pwd)                                   # repro/eight
ROOT=$(cd "$E/../.." && pwd)                             # repository root (parent of lean/ and repro/)
LM=$ROOT/lean
GEN=$E/bin/l7v4s                                         # built by build_generator.sh
W=$S/work                                                # staging: sources, oleans, logs, new records
REC=$E/records                                           # committed records (read only here)
mkdir -p "$W/logs" "$W/records"

#!/usr/bin/env bash
# Capture before/after logical plan pairs for each query in queries/.
#
#   <name>_before.json  -- PRAGMA disable_optimizer (raw plan from binder)
#   <name>_after.json   -- only `filter_pushdown` enabled
#   duckdb_version.txt  -- pinned DuckDB version

set -euo pipefail

cd "$(dirname "$0")"
mkdir -p plans

duckdb -noheader -list -c "SELECT version();" > plans/duckdb_version.txt

ALL_EXCEPT_FP=$(duckdb -noheader -list \
  -c "SELECT string_agg(name, ',') FROM duckdb_optimizers() WHERE name <> 'filter_pushdown';")

dump_plan() {
  local setup="$1" disable_line="$2" query="$3" out="$4"
  duckdb 2>/dev/null <<EOF | awk '/^\[/{f=1} f' > "$out"
$setup
$disable_line
SET explain_output='optimized_only';
EXPLAIN (FORMAT JSON) $query;
EOF
}

for sql_file in queries/*.sql; do
  name=$(basename "$sql_file" .sql)
  setup=$(awk '/^-- EXPLAIN:/{exit} {print}' "$sql_file")
  query=$(awk 'f; /^-- EXPLAIN:/{f=1}' "$sql_file" | sed 's/;[[:space:]]*$//')

  dump_plan "$setup" "PRAGMA disable_optimizer;" "$query" "plans/${name}_before.json"
  dump_plan "$setup" "SET disabled_optimizers='$ALL_EXCEPT_FP';" "$query" "plans/${name}_after.json"

  echo "captured: $name"
done

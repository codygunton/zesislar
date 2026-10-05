#!/usr/bin/env bash
set -euo pipefail
exec "${ZESU_MCP_PYTHON:?use the pinned MCP Python}" "$(dirname "$(realpath "$0")")/complete_goals_mcp.py"

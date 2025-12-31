#!/bin/bash

# This script builds the project's Lean code.

set -o pipefail # stop if any command fails
export LAKE_ARTIFACT_CACHE=false

cd analysis/
lake exe cache get
lake build

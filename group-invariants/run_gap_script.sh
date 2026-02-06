#!/bin/bash

# Read the GAP script file and send it via curl
curl -s -X POST -d "$(cat count_groups.gap)" https://gap-test-bmhkf.sprites.app

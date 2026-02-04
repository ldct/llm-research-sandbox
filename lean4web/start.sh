#!/bin/bash
export NVM_DIR="/home/exedev/.nvm"
[ -s "$NVM_DIR/nvm.sh" ] && \. "$NVM_DIR/nvm.sh"
export PATH="/home/exedev/.elan/bin:$PATH"
nvm use 25

cd /home/exedev/lean4web
exec env PORT=8000 ALLOW_NO_BUBBLEWRAP=true node server/index.mjs

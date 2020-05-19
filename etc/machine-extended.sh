#!/bin/sh

echo '+ lscpu'
lscpu || true
echo '+ uname -a'
uname -a || true
echo '+ lsb_release -a'
lsb_release -a || true

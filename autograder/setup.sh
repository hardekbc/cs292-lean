#!/usr/bin/env bash

COURSE_REPO="https://github.com/hardekbc/cs292-lean"

echo "installing elan"
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y
~/.elan/bin/lean --version

apt-get install -y python3 python3-pip python3-dev git

cd /autograder/source

echo "cloning $COURSE_REPO"
git init 
git remote add origin "$COURSE_REPO.git"
git fetch origin 
MAIN_BRANCH=$(git remote show origin | sed -n '/HEAD branch/s/.*: //p')
git reset --hard origin/$MAIN_BRANCH

echo "building applications"
~/.elan/bin/lake exe cache get 
~/.elan/bin/lake build Course comparator lean4export

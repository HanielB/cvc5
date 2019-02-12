#!bin/bash

# USAGE:
# sh fetch-ajreynol.sh branch-to-diff

# Logic follows this thread:
# https://stackoverflow.com/questions/5884784/how-to-pull-remote-branch-from-somebody-elses-repo

##########################################

# only need to do this once per clone:
# git remote add ajreynol git@github.com:ajreynol/CVC4.git

git fetch ajreynol
git checkout --track ajreynol/$1
# The above will setup a local branch foo, tracking the remote branch
# coworker/foo. So when your co-worker has made some changes, you can
# easily pull them:
git checkout $1
git pull

##########################################
# diff-ing  with magit:
#
# M-x magit-diff
# range is master..branch

#!bin/bash

git diff -U0 -w | git apply --cached --ignore-whitespace --unidiff-zero -

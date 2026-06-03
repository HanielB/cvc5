#!/usr/bin/env bash
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Download a prebuilt SCIP Optimization Suite (https://www.scipopt.org)
# release into deps/install, where cvc5's build system picks it up
# automatically (configure with --scip).
#
# cvc5 requires SCIP >= 10.0 with exact rational solving support
# (Apache-2.0 licensed since SCIP 8.0.3).
#
# Alternatives to this script:
#   - a system package providing SCIP >= 10.0, or
#   - a manual installation, passed to configure via --scip-dir=PATH.
#
# The version can be overridden, e.g.: SCIP_VERSION=10.0.2 contrib/get-scip.sh
##

source "$(dirname "$0")/get-script-header.sh"

SCIP_VERSION="${SCIP_VERSION:-10.0.2}"

# Prebuilt portable tarballs are published on the SCIP GitHub releases page.
case "$(uname -s)-$(uname -m)" in
  Linux-x86_64)
    # Pick the tarball matching the system's glibc.
    GLIBC_MINOR="$(ldd --version 2>/dev/null | head -1 | grep -o '2\.[0-9]*$' \
                   | cut -d. -f2)"
    if [ -n "$GLIBC_MINOR" ] && [ "$GLIBC_MINOR" -lt 34 ]; then
      PKG="scipoptsuite-${SCIP_VERSION}-glibc2_28-amd64.tgz"
    else
      PKG="scipoptsuite-${SCIP_VERSION}-glibc2_34-amd64.tgz"
    fi
    ;;
  Linux-aarch64)
    PKG="scipoptsuite-${SCIP_VERSION}-glibc2_28-aarch64.tgz"
    ;;
  Darwin-arm64)
    PKG="scipoptsuite-${SCIP_VERSION}-macos13-arm64.tgz"
    ;;
  *)
    echo "Error: no prebuilt SCIP for $(uname -s)/$(uname -m); install SCIP" \
         "manually and use --scip-dir=PATH." >&2
    exit 1
    ;;
esac

URL="https://github.com/scipopt/scip/releases/download/v${SCIP_VERSION}/${PKG}"

SCIP_TMP_DIR="$DEPS_DIR/tmp-scip"
rm -rf "$SCIP_TMP_DIR"
mkdir -p "$SCIP_TMP_DIR"
cd "$SCIP_TMP_DIR"

echo "Downloading $URL"
webget "$URL" "$PKG"

mkdir -p extracted
tar -xf "$PKG" -C extracted --strip 1

mkdir -p "$INSTALL_DIR"
cp -a extracted/. "$INSTALL_DIR/"

cd "$DEPS_DIR"
rm -rf "$SCIP_TMP_DIR"

# Sanity checks.
if [ ! -r "$INSTALL_INCLUDE_DIR/scip/scip.h" ]; then
  echo "Error: scip/scip.h not found under $INSTALL_INCLUDE_DIR after" \
       "installation." >&2
  exit 1
fi

SCIP_LIB="$(find "$INSTALL_DIR" -name 'libscip*' | head -1)"
if [ -z "$SCIP_LIB" ]; then
  echo "Error: libscip not found under $INSTALL_DIR after installation." >&2
  exit 1
fi

# Verify the build supports exact rational solving (required by cvc5).
if ! grep -rq "SCIPenableExactSolving" "$INSTALL_INCLUDE_DIR/scip/"; then
  echo "Error: this SCIP installation does not declare exact solving" \
       "support; cvc5 requires SCIP >= 10.0 with exact solving enabled." >&2
  exit 1
fi

echo
echo "SCIP $SCIP_VERSION installed to $INSTALL_DIR"
echo "Now configure cvc5 with: ./configure.sh --scip"

###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find SCIP (https://www.scipopt.org), the solver of the SCIP Optimization
# Suite. cvc5 requires a SCIP build with support for exact rational solving
# (SCIP 10.0 or later, compiled with exact solving enabled).
#
# In contrast to other optional dependencies, no ExternalProject fallback is
# provided: install SCIP via contrib/get-scip.sh (prebuilt release into
# deps/install), a system package, or point --scip-dir=PATH to an existing
# installation.
#
# SCIP_FOUND - system has the SCIP lib
# SCIP_INCLUDE_DIR - the SCIP include directory
# SCIP_LIBRARIES - Libraries needed to use SCIP
##

find_path(SCIP_INCLUDE_DIR NAMES scip/scip.h)
# Note: prebuilt SCIP releases install their libraries under lib64.
find_library(SCIP_LIBRARIES NAMES scip PATH_SUFFIXES lib lib64)

if(NOT SCIP_INCLUDE_DIR OR NOT SCIP_LIBRARIES)
  message(FATAL_ERROR
    "Could not find SCIP. Install it via contrib/get-scip.sh, a system "
    "package providing SCIP >= 10.0 with exact solving support, or configure "
    "with --scip-dir=PATH.")
endif()

# Require a SCIP build with exact rational solving support (SCIP >= 10.0
# compiled with exact arithmetic enabled). The check links against the
# entry point for enabling exact solving.
include(CheckSymbolExists)
set(CMAKE_REQUIRED_INCLUDES ${SCIP_INCLUDE_DIR})
set(CMAKE_REQUIRED_LIBRARIES ${SCIP_LIBRARIES})
check_symbol_exists(SCIPenableExactSolving "scip/scip.h" HAVE_SCIP_EXACT)
unset(CMAKE_REQUIRED_INCLUDES)
unset(CMAKE_REQUIRED_LIBRARIES)
if(NOT HAVE_SCIP_EXACT)
  message(FATAL_ERROR
    "The SCIP installation at ${SCIP_LIBRARIES} does not support exact "
    "rational solving. cvc5 requires SCIP >= 10.0 built with exact solving "
    "enabled (see contrib/get-scip.sh).")
endif()

set(SCIP_FOUND TRUE)
set(SCIP_FOUND_SYSTEM TRUE)

add_library(SCIP UNKNOWN IMPORTED GLOBAL)
set_target_properties(SCIP PROPERTIES
    IMPORTED_LOCATION "${SCIP_LIBRARIES}"
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${SCIP_INCLUDE_DIR}"
)

mark_as_advanced(SCIP_FOUND)
mark_as_advanced(SCIP_FOUND_SYSTEM)
mark_as_advanced(SCIP_INCLUDE_DIR)
mark_as_advanced(SCIP_LIBRARIES)

message(STATUS "Found SCIP: ${SCIP_LIBRARIES}")

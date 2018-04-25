#!/bin/bash

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then  xvfb-run ./make.py --enable-long-tests; fi
if [[ "$TRAVIS_OS_NAME" == "osx"   ]]; then  ./make.py --disable-threads --disable-tests; fi
if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then  xvfb-run ./make.py --enable-long-tests --cc=clang; fi
if [[ "$TRAVIS_OS_NAME" == "osx"   ]]; then  ./make.py --disable-threads --disable-tests --cc=clang; fi

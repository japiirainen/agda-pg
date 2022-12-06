#!/usr/local/bin/bash

agda -c src/Main.agda --ghc-flag="-o" --ghc-flag="Main" --compile-dir=_build

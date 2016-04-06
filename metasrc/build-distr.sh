#!/bin/sh

set -e

./make-tutorial.sh
chmod 644 *.css *.html *.v
cp main.css coqdoc.css paco*.html tutorial.html paco/doc/
cp hpattern.v paco*.v tutorial.v paco/src/


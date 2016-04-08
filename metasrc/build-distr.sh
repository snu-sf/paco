#!/bin/sh

set -e

title="paco Tutorial"
coqdoc -s --no-index --html paco*.v tutorial.v
sed -i "s,<title>tutorial</title>,<title>$title</title>," tutorial.html

mkdir -p paco paco/src paco/doc 
chmod 644 *.css *.html *.v
cp main.css coqdoc.css paco*.html tutorial.html paco/doc/
cp hpattern.v paco*.v tutorial.v paco/src/
cp README CHANGES LICENSE paco/

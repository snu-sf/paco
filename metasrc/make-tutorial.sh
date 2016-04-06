#!/bin/sh

set -e

title="paco Tutorial"

make tutorial.vo
coqdoc -s --no-index --html paco*.v tutorial.v
sed -i "s,<title>tutorial</title>,<title>$title</title>," tutorial.html
cp coqdoc_edited.css coqdoc.css

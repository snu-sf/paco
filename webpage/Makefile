##
# Alectryon paco tutorial
#
# @file
# @version 0.1

tutorial.html:
	alectryon ../src/tutorial.v -o tutorial.rst
	alectryon --frontend coq+rst --backend rst ../src/tutorial.v -o tutorial.rst
	alectryon tutorial.rst
	alectryon --frontend rst --backend webpage tutorial.rst -o tutorial.html

open: tutorial.html
	xdg-open tutorial.html

clean:
	rm -f *.css *.js *.rst *.html

# end

#!/bin/sh

# (C) Copyright 2010, COQTAIL team
# 
# Project Info: http://sourceforge.net/projects/coqtail/
# 
# This library is free software; you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation; either version 2.1 of the License, or
# (at your option) any later version.
# 
# This library is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
# License for more details.
# 
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
# USA.

# subscript of the Makefile to generate a correct documentation

rev=`svn info --xml | grep revision= | sed 's/.*revision="\([0-9]*\)".*$/\1/' | head -n 1`
mkdir -p doc
cd doc
if [ -f index.html ]
then
	rm index.html
	
	echo '<h2>Documentation (r' >> list
	echo $rev >> list
	echo ')</h2><div id="main">' >> list
	for i in `ls *.html | sed 's/\..*//' | uniq`
	do
		echo "<h2 class=\"doc\">$i</h2>" >> list
		echo "<ul>" >> list
		ls $i*.html | sed 's/^\(.*\)\.\(.*\).html$/<li><a href="main.php?page=3&amp;doc=\1.\2">\2<\/a><\/li>/' >> list
		echo "</ul>" >> list
	done
	mv list index.html
	cp ../coqdoc.css .
	cp ../index.css .

else
	echo "index.html not found. Script should be called by make"
fi
cd ..


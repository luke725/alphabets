#!/bin/bash

# author: Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)
# a script for generating all representatives of conjugacy classes of S_n, where n is $1
# output of the script can be used as an input of [alphabets all]

echo "List(List(ConjugacyClassesSubgroups(SymmetricGroup($1)), Representative), GeneratorsOfGroup);" | gap -q | sed s/\)\(/],[/g | sed -e s/\(/[[/g -e s/\)/]]/g


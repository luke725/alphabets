#!/bin/bash

echo "List(List(ConjugacyClassesSubgroups(SymmetricGroup($1)), Elements), l->List(l,GeneratorsOfGroup));" | gap -q | sed s/\)\(/],[/g | sed -e s/\(/[[/g -e s/\)/]]/g


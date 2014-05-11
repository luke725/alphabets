#!/bin/bash

echo "List(List(ConjugacyClassesSubgroups(SymmetricGroup(6)), Representative), GeneratorsOfGroup);" | gap -q | sed s/\)\(/],[/g | sed -e s/\(/[[/g -e s/\)/]]/g


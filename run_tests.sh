#!/usr/bin/env bash

my_errs=()

for file in code/*.ppl
do
    printf '%-40s' "Compiling ${file}... "
    my_err=$(./compiler.exe < $file 2>&1 > /dev/null)
    if [ $? = 0 ]
    then
        echo "Success"
    else
        echo "Failure"
        my_errs+="Error in ${file}: ${my_err}
"
    fi
done

cat <<EOF
$my_errs
EOF

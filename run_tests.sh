#!/usr/bin/env bash

round () {
    # Round all floats to 1 decimal place.
    perl -pe 's/(-?\d+(\.\d+)?)/sprintf("%.1f",$1)/ge'
}

my_errs=()

for file in \
    examples/{amb,datatype_polymorphism,derefun,double,dyck,equal,example12,extinction,fsm,fsm2,function_polymorphism,head_tail_rec,pattern1,pattern2,pda,pda2,penney,products,reverse,sample,stairs,syntax,tree,von_neumann}.ppl \
    tests/good/{type_parameter_nonrecursive,type_parameter_unused,zero_add_prod}.ppl
do
    printf '%-40s' "Compiling ${file}... "
    my_err=$(./perplc $file -o /dev/null 2>&1 > /dev/null)
    if [ $? = 0 ]
    then
        echo "Success"
    else
        echo "Failure"
        my_errs+="Error in ${file}: ${my_err}
"
    fi

    correct=$(perl -ne 'if (/correct: (.*)/) { print $1; }' $file | round)
    if [ -n "$correct" ]; then
        printf '%-40s' "Running ${file}... "
        out=$(./perplc -z $file 2> /dev/null | round)
        if [ "$correct" = "$out" ]; then
            echo "Success"
        else
            echo "Failure"
            my_errs+="Incorrect result in ${file}: ${correct} != ${out}"
        fi
    fi
done

for file in tests/bad/{type_mismatch,case_of_zero_cases,case_without_bar,data_with_zero_cons,data_without_bar,infinite_extern,type_parameter_{different,swap,copy,double},polymorphic_recursion,answer_function,answer_recursive,answer_amp,elim_zero_add_prod}.ppl
do
    printf '%-40s' "Compiling ${file}... "
    my_err=$(./perplc $file -o /dev/null 2>&1 > /dev/null)
    if [ $? != 0 -a -f "$file" ]
    then
        echo "Success"
    else
        echo "Failure"
    fi
done

cat <<EOF
$my_errs
EOF

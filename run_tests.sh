#!/usr/bin/env bash

round () {
    # Round all floats to 1 decimal place.
    perl -pe 's/(-?\d+(\.\d+(e-?\d+)?)?)/sprintf("%.1f",$1)/ge; s/ //g;'
}

my_errs=()

for file in \
    examples/{bool,dyck,extinction,fsm,list,nat,parser,pattern1,pattern2,pda,penney,reverse,stairs,tree,von_neumann}.ppl \
    tests/good/{amb,fail,sample,products,type_parameter_{nonrecursive,unused,different,swap},{zero,one,discard}_add_prod,datatype_containing_type_application,partial_application{,_recursive},{amb,factor}_lambda_{0,1,2},function_polymorphism,infinite_fails,case_lambda,discard_prods,forall_positive_unused_type_parameter}.ppl
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

for file in tests/bad/{type_mismatch,case_of_zero_cases,case_without_bar,data_with_zero_cons,data_without_bar,infinite_extern,type_parameter_different,type_parameter_swap,polymorphic_recursion,polymorphic_type_recursion{,2},answer_function,answer_recursive,answer_amp,elim_zero_add_prod,unbound_type_var,forall_positive,nonlinear_let}.ppl
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

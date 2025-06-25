#!/usr/bin/env bash

round () {
    # Round all floats to 1 decimal place.
    perl -pe 's/(-?\d+(\.\d+(e-?\d+)?)?)/sprintf("%.1f",$1)/ge; s/ //g;'
}

my_errs=()

for file in \
    examples/{bool,dyck,extinction,fsm,list,nat,parser,pattern1,pattern2,pda,penney,reverse,stairs,tree,von_neumann,von_neumann_pair}.ppl \
    tests/good/{amb,fail,sample,products,type_parameter_{nonrecursive,unused,different,swap},{zero,one,discard}_add_prod,datatype_containing_type_application,partial_application{,_recursive},{amb,factor}_lambda_{0,1,2},function_polymorphism,infinite_fails,case_lambda,discard_prods,forall_positive_unused_type_parameter,shadow_local_over_{ctor,datatype},tm_var_name,define_func_lhs,global_name_shadowing,syntax_types,rec_compare_{0,1,2},answer_{function,recursive,amp},nat_num_{0,1,2,3,4,5,6},rational_factor_{0,1,2}}.ppl
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

echo    # print newline to separate good and bad tests

for file in tests/bad/{type_mismatch,case_of_zero_cases,case_without_bar,data_with_zero_cons,data_without_bar,infinite_extern,type_parameter_different,type_parameter_swap,polymorphic_recursion,polymorphic_type_recursion{,2},elim_zero_add_prod,unbound_type_var,forall_positive,nonlinear_let,compare_{0,1},nat_num_bad_{0,1,2}}.ppl
do
    printf '%-40s' "Compiling ${file}... "
    my_err=$(./perplc $file -o /dev/null 2>&1 > /dev/null)
    if [ $? != 0 ] && [ -f "$file" ]
    then
        echo "Success"
    else
        echo "Failure"
    fi
done

cat <<EOF
$my_errs
EOF

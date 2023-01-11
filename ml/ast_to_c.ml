open Ast

let ast_to_c ast_list = 
    begin
        Format.printf "%s\n%s\n%s\n%s\n%s\n\t%s\t%s\n"
            "#include <assert.h>"
            "#include <stdio.h>"
            "#include <stdlib.h>"
            "int const N = 30000;"
            "int main(){"
                "int *ptr = malloc(N * sizeof(int));"
                "for (int i=0; i<N; i++) ptr[i] = 0;"
        ;

        let number_tab = ref 1 in

        let rec print_op op = begin
            for i = 0 to !number_tab-1 do
                Format.printf "\t"
            done;

            match op.expr with 
            | Right -> Format.printf "ptr++;\n"
            | Left  -> Format.printf "ptr--;\n"
            | Incr  -> Format.printf "(*ptr)++;\n"
            | Decr  -> Format.printf "(*ptr)--;\n"
            | Error -> Format.printf "assert(0);\n"
            | Read  -> Format.printf "(*ptr) = getchar();\n"
            | Write -> Format.printf "putchar(*ptr);\n"

            | While liste -> begin
                number_tab := !number_tab + 1;
                Format.printf "while (*ptr){\n";
                List.iter print_op liste;
                number_tab := !number_tab - 1;

                for i=0 to !number_tab-1 do
                    Format.printf "\t"
                done;

                Format.printf "}\n"
            end
        end
        in

        List.iter print_op ast_list;

        Format.printf "}\n\n"



    end
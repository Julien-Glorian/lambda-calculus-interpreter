open List;;


(**
    This type represents a lambda-term with a tree.

    A lambda-term can be represented with three differents things :
    1) Variable, which represents a variable
    2) Lambda, which represents a lambda followed by an other lambda-term
    3) Application, which represents two lambda-terms side by side

    With this representation, we can construct all lambda-terms possibles non-empty.
    *)

type lambda_term =
    | Variable of int
    | Lambda of lambda_term
    | Application of lambda_term * lambda_term
;;


(**
    This function constructs the string associated with the given lambda-term.
    The string is in correlation with the notation of De Breijn's index.
    
    The string retourned contains not the minimal number of parentheses, but we are really close (it adds parenthesis when
    we have a redex, even if the application concerns a unique variable) This representation is for me the most understandable.
    Also, this string can be reversed in a lambda-term because the transformation is deterministic. I want to code this.
    
    Here is the list of conditions to construct the string :
    1) if the lambda-term is a variable, we just note the variable
    2) if the lambda-term is a lambda :
        a) if the lambda-term inside is also lambda, we just note the first lambda
        b) if the lambda-term inside is not a lambda, we note the first lambda and add a point
    and we continue with the lambda-term inside
    3) if the lambda-term is an application
        a) if the left lambda-term is a lambda, we have a redex so add parentheses around left and right lambda-terms
        b) if the left lambda-term is not a lambda :
            i) if the right lambda-term is a variable, we just note left and right lambda-terms
            ii) if the right lambda-term is not a variable, we add parenteses just around the right lambda-term
    and we continue for the left lambda-term and the right lambda-term

    For the sake of understanding, we add a "x" for all variables, follow up by its int.
    *)

let string_of_lambda_term : lambda_term -> string = fun term ->
    let rec string_of_lambda_term_intern : lambda_term -> string = fun term ->
        match term with
        | Variable(index) -> "x" ^ (string_of_int index)
        | Lambda(term_bound) -> "λ" ^ (
            match term_bound with
            | Lambda(_) -> ""
            | _ -> "."
            ) ^ (string_of_lambda_term_intern term_bound)
        | Application(term_left, term_right) -> (
            match term_left with
            | Lambda(_) -> "(" ^ (string_of_lambda_term_intern term_left) ^ ")(" ^ (string_of_lambda_term_intern term_right) ^ ")"
            | _ -> (string_of_lambda_term_intern term_left) ^ (
                match term_right with
                | Variable(_) -> (string_of_lambda_term_intern term_right)
                | _ -> "(" ^ (string_of_lambda_term_intern term_right) ^ ")"
            )
        )
    in (string_of_lambda_term_intern term) ^ "\n"
;;


(**
    This function checks if the lambda-term given is directly a beta-redex.

    The lambda term is directly a beta-redex if it's an application with the right lambda-term equivalent to a lambda.
    *)

let is_beta_redex : lambda_term -> bool = fun term ->
    match term with
    | Application(Lambda(_),_) -> true
    | _ -> false
;;


(**
    This function checks if a lambda-term is in beta-normal-form.
    
    A lambda-term is in beta-normal-form if it contains not a beta-redex.
    *)

let rec is_beta_normal_form : lambda_term -> bool = fun term ->
    if (is_beta_redex term) then false else (
        match term with
        | Variable(_) -> true
        | Lambda(term_bound) -> is_beta_normal_form term_bound
        | Application(term_left, term_right) -> (is_beta_normal_form term_left) && (is_beta_normal_form term_right)
    )
;;


(**
    This function checks if a lambda-term is closed.
        
    A lambda-term is closed if all its variables are associated with a lambda and consequently are bounds.
    *)

let is_closed : lambda_term -> bool = fun term ->
    let rec is_closed_intern : lambda_term -> int -> bool = fun term_intern abstraction_level ->
        match term_intern with
        | Variable(index) -> index <= abstraction_level
        | Lambda(term_bound) -> is_closed_intern term_bound (abstraction_level + 1)
        | Application(term_left, term_right) -> (is_closed_intern term_left abstraction_level) && (is_closed_intern term_right abstraction_level)
    in is_closed_intern term 0
;;


(**
    This function makes a beta-reduction left with a renaming of all variables substituate.
    For information, the program use the notation of De Breijn's index.
    
    The function constructs the new lambda term with a list of actions defined, and we can remark there are three important
    steps for this function.

    1) First step (five last lines) : find the first redex
        a) if the lambda-term is a variable, we just note the variable
        b) if the lambda-term is a lambda, we call the first step inside the lambda
        c) if the lambda-term is a redex, we call the second step with this application
        d) if the lambda-term is an application :
            i) if the left-hand side is in beta normal form, we call the first step on the right-hand side
            ii) else we call the first step on the left-hand side

    2) Second step (in the middle) : substitution
        a) if the lambda-term is a variable
            i) if the index is equal to the abstraction level we substitute this term and call third step
            ii) if the index is greater than the abstraction level we have a free variable in this term, as we delete a lambda
                the variable is now one level lower
            iii) else we just note the variable
        b) if the lambda-term is a lambda we call second step with one level abstraction higher
        c) if the lambda-term is an application, we call second step on the left-hand side and right-hand side
    
    3) Third step (at the top) : normalize substitution
        a) if the lambda-term is a variable
            i) if the index is greater than the abstraction level, its new value is its old index minus one plus the index of 
                the substituate variable
            ii) else we just note the variable
        b) if the lambda-term is a lambda we call third step with one level abstraction higher
        c) if the lambda-term is an application, we call third step on the left-hand side and right-hand side
    *)

let rec beta_reduction_left : lambda_term -> lambda_term = fun term ->
    let rec normalize_substitution : lambda_term -> int -> int-> lambda_term = fun term_substituate index_variable_substituate abstraction_level_intern ->
        match term_substituate with
        | Variable(index) -> if index > abstraction_level_intern then Variable(index - 1 + index_variable_substituate) else Variable(index)
        | Lambda(term_bound) -> Lambda(normalize_substitution term_bound index_variable_substituate (abstraction_level_intern + 1))
        | Application(term_left, term_right) -> Application(normalize_substitution term_left index_variable_substituate abstraction_level_intern, normalize_substitution term_right index_variable_substituate abstraction_level_intern)
    in let rec substitution : lambda_term -> int -> lambda_term -> lambda_term = fun term_base abstraction_level term_change ->
        match term_base with
        | Variable(index) -> if index = abstraction_level then (normalize_substitution term_change index 0) else if index > abstraction_level then Variable(index - 1) else Variable(index)
        | Lambda(term_bound) -> Lambda(substitution term_bound (abstraction_level + 1) term_change)
        | Application(term_left, term_right) -> Application(substitution term_left abstraction_level term_change, substitution term_right abstraction_level term_change)
    in match term with
    | Variable(index) -> Variable(index)
    | Lambda(term_bound) -> Lambda(beta_reduction_left term_bound)
    | Application(Lambda(term_to_change), term_to_substitute) -> substitution term_to_change 1 term_to_substitute
    | Application(term_left, term_right) -> if is_beta_normal_form term_left then Application(term_left, beta_reduction_left term_right) else Application(beta_reduction_left term_left, term_right)
;;


(*The next part will show some functions to encode and calculate numbers with the Church's encoding number.*)


(**
    This function checks if the lambda-term given is a number with Church's encoding number.
    *)

let is_number_form : lambda_term -> bool = fun term ->
    let rec verification_intern : lambda_term -> bool = fun term_intern ->
        match term_intern with
        | Variable(1) -> true
        | Application(Variable(2), term_right) -> verification_intern term_right
        | _ -> false
    in match term with
    | Lambda(Lambda(term_bound)) -> verification_intern term_bound
    | _ -> false
;;


(**
    This function calculate the number associated with a lambda-term if it is in Church's encoding.
    *)

let evaluate_number : lambda_term -> int = fun term ->
    let rec count : lambda_term -> int -> int = fun term_intern number ->
        match term_intern with
        | Variable(1) -> number
        | Application(Variable(2), term_right) -> count term_right (number + 1)
        | _ -> -1
    in match term with
    | Lambda(Lambda(term_bound)) -> count term_bound 0
    | _ -> -1
;;


(**
    This function makes multiple beta-reduction left.
    *)

let rec multiple_beta_reduction_left : lambda_term -> int -> lambda_term = fun term nb_reduction ->
    if (is_beta_normal_form term || nb_reduction = 0) then term else multiple_beta_reduction_left (beta_reduction_left term) (nb_reduction - 1)
;;


(**
    This function makes beta-reduction left until it obtains a beta-normal form on a given lambda-term.
    This function has no stop point if the lambda-term loops or diverges. 
    *)

let rec beta_reduction_left_until_beta_normal_form : lambda_term -> lambda_term = fun term ->
    if is_beta_normal_form term then term else beta_reduction_left_until_beta_normal_form (beta_reduction_left term)
;;


(**
    This function calculates the successor of a Church's encoding number.
    *)

let successor : lambda_term -> lambda_term = fun term ->
    let term_successor : lambda_term = Lambda(Lambda(Lambda(Application(Variable(2), Application(Application(Variable(3), Variable(2)), Variable(1))))))
in beta_reduction_left_until_beta_normal_form (Application(term_successor, term));;


(**
    This function calculates the addition of two Church's encoding numbers.
    *)

let addition : lambda_term -> lambda_term -> lambda_term = fun term_left term_right ->
    let term_addition : lambda_term = Lambda(Lambda(Lambda(Lambda(Application(Application(Variable(4), Variable(2)), Application(Application(Variable(3), Variable(2)), Variable(1)))))))
in beta_reduction_left_until_beta_normal_form (Application(Application(term_addition, term_left), term_right));;


(**
    This function calculates the multiplication of two Church's encoding numbers.
    *)

let multiplication : lambda_term -> lambda_term -> lambda_term = fun term_left term_right ->
    let term_multiplication : lambda_term = Lambda(Lambda(Lambda(Application(Variable(3), Application(Variable(2), Variable(1))))))
in beta_reduction_left_until_beta_normal_form (Application(Application(term_multiplication, term_left), term_right));;


(*The next part will show the addition and multiplication with Turing's fix point.*)


(**
    This lambda-term represents the turing's fix point.
    *)

let theta : lambda_term = Application(
    Lambda(Lambda(Application(Variable(1), Application(Application(Variable(2), Variable(2)), Variable(1))))),
    Lambda(Lambda(Application(Variable(1), Application(Application(Variable(2), Variable(2)), Variable(1)))))
);;


(**
    This lambda-term represents the zero test.

    If it's applicate with a Church's encoding number, it will returns λλ.x2 if it's true and λλ.x1 if it's false.
    *)

let is_zero : lambda_term = Lambda(Lambda(Lambda(Application(Application(Variable(3), Lambda(Variable(2))), Variable(2)))));;


(**
    This lambda-term represents zero according to Church's encoding number.
    *)
let zero : lambda_term = Lambda(Lambda(Variable(1)));;


(**
    This lambda-term represents the successor term.

    If it's applicate with one number, it will returns the next number.
    *)

let succ : lambda_term = Lambda(Lambda(Lambda(Application(Variable(2), Application(Application(Variable(3), Variable(2)), Variable(1))))));;


(**
    This lambda-term represents the predessessor term.

    If it's applicate with one number, it will returns the previous number.
    *)

let pred : lambda_term = 
    Lambda(
        Lambda(
            Lambda(
                Application(
                    Application(
                        Application(
                            Variable(3),
                            Lambda(
                                Lambda(
                                    Application(
                                        Variable(1),
                                        Application(
                                            Variable(2),
                                            Variable(4)
                                        )
                                    )
                                )
                            )
                        ),
                        Lambda(
                            Variable(2)
                        )
                    ),
                    Lambda(
                        Variable(1)
                    )
                )
            )
        )
    )
;;


(**
    This lambda-term represents the if_then_else function.

    It's the same encoding than the identity function, because the action is define directy in the encoding of the terms true and false.
    *)

let if_then_else : lambda_term = Lambda(Variable(1));;


(**
    This function represents the lambda-term of addition of two Chursh's encoding numbers using the turing's fix point.

    If it applicate with two numbers, it will returns their addition.
    *)

let add : lambda_term =
    Application(
        theta,
        Lambda(
            Lambda(
                Lambda(
                    Application(
                        Application(
                            Application(
                                if_then_else,
                                Application(
                                    is_zero,
                                    Variable(2)
                                )
                            ),
                            Variable(1)
                        ),
                        Application(
                            Application(
                                Variable(3),
                                Application(
                                    pred,
                                    Variable(2)
                                )
                            ),
                            Application(
                                succ,
                                Variable(1)
                            )
                        )
                    )
                )
            )
        )
    )
;;


(**
    This function represents the lambda-term of multiplication of two Chursh's encoding numbers using the turing's fix point.

    If it applicate with two numbers, it will returns their multiplication.
    *)

let mult : lambda_term =
    Application(
        theta,
        Lambda(
            Lambda(
                Lambda(
                    Application(
                        Application(
                            Application(
                                if_then_else,
                                Application(
                                    is_zero,
                                    Variable(2)
                                )
                            ),
                            zero
                        ),
                        Application(
                            Application(
                                add,
                                Variable(1)
                            ),
                            Application(
                                Application(
                                    Variable(3),
                                    Application(
                                        pred,
                                        Variable(2)
                                    )
                                ),
                                Variable(1)
                            )
                        )
                    )
                )
            )
        )
    )
;;


(*Tests zone*)

(*let number_zero : lambda_term = Lambda(Lambda(Variable(1)));;
let number_one : lambda_term = Lambda(Lambda(Application(Variable(2), Variable(1))));;
let number_two : lambda_term = Lambda(Lambda(Application(Variable(2), Application(Variable(2), Variable(1)))));;
let number_four : lambda_term = addition number_two number_two;;
let number_five : lambda_term = successor number_four;;

let number_nine : lambda_term = beta_reduction_left_until_beta_normal_form (Application(Application(add, number_four), number_five));;
let number_twenty1 : lambda_term = beta_reduction_left_until_beta_normal_form (Application(Application(mult, number_four), number_five));;
let number_twenty2 : lambda_term = beta_reduction_left_until_beta_normal_form (Application(Application(mult, number_five), number_four));;

print_string (string_of_lambda_term number_nine);;
print_string ((string_of_int (evaluate_number number_twenty1)) ^ "\n");;
print_string ((string_of_int (evaluate_number number_twenty2)) ^ "\n");;*)

(*let number_unkwown1 : lambda_term = multiplication number_four number_five;;
let number_unkwown2 : lambda_term = multiplication number_five number_four;;


let print_bool : bool -> unit = fun boolean ->
    if boolean then print_string "yes\n" else print_string "no\n"
;;

let print_int : int -> unit = fun integer ->
    print_string (string_of_int integer ^ "\n")
;;

print_int (evaluate_number number_zero);;
print_int (evaluate_number number_one);;
print_int (evaluate_number number_two);;
print_int (evaluate_number number_four);;
print_int (evaluate_number number_five);;
print_int (evaluate_number number_unkwown1);;
print_int (evaluate_number number_unkwown2);;*)





(*let a : lambda_term = Lambda(Lambda(Application(Variable(1), Application(Application(Variable(2), Variable(2)), Variable(1)))));;
let turing_fix_point : lambda_term = Application(a,a);;

let a2 : lambda_term = Lambda(Lambda(Application(Variable(1), Application(Application(Variable(3), Variable(2)), Variable(1)))));;

print_string (string_of_lambda_term a);;
print_string (string_of_lambda_term turing_fix_point);;



print_bool (is_beta_normal_form a);;
print_bool (is_beta_normal_form turing_fix_point);;

print_bool (is_closed a);;
print_bool (is_closed turing_fix_point);;
print_bool (is_closed a2);;*)

(*let b : lambda_term = beta_reduction_left(turing_fix_point);;
print_string (string_of_lambda_term b);;
let b2 : lambda_term = beta_reduction_left(b);;
print_string (string_of_lambda_term b2);;
let b2 : lambda_term = beta_reduction_left(b2);;
print_string (string_of_lambda_term b2);;
let b2 : lambda_term = beta_reduction_left(b2);;
print_string (string_of_lambda_term b2);;
let b2 : lambda_term = beta_reduction_left(b2);;
print_string (string_of_lambda_term b2);;
let b2 : lambda_term = beta_reduction_left(b2);;
print_string (string_of_lambda_term b2);;

let bizarre = Application(a2,a2);;
print_string (string_of_lambda_term bizarre);;
let bizarre2 = beta_reduction_left(bizarre);;
print_string (string_of_lambda_term bizarre2);;*)

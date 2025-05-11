import time

# Global Variables
dp = False # global declaration, value doesn't matter
clause_list = list()
# ----------------------

def clause_split1 (og_input):
    # Returns clauses split in a list in the order of the original input
    clist = list()
    input_length = len(og_input)
    index = -1
    while index < input_length:
        # Splits the input into a list of clauses
        ok = 0
        clause = ''
        if og_input[index] == '[':
            index += 1
            ok = 1
            while og_input[index] != ']':
                clause += og_input[index]
                index += 1
        if ok:
            clist.append(clause)
        index += 1
    return clist

def resolve(aux1, aux2):
    clause1 = aux1.split(',')
    clause2 = aux2.split(',')
    complementary_check = False
    index_c1 = 0

    while index_c1 < len(clause1):
        index_c2 = 0
        while index_c2 < len(clause2):
            if len(clause1[index_c1]) == 2:
                if clause1[index_c1][1] == clause2[index_c2]:
                    complementary_check = True
                    clause1.pop(index_c1)
                    clause2.pop(index_c2)
                    index_c1 -= 1
                    break
            elif '!' + clause1[index_c1] == clause2[index_c2]:
                complementary_check = True
                clause1.pop(index_c1)
                clause2.pop(index_c2)
                index_c1 -= 1
                break
            index_c2 += 1

        if complementary_check:
            break
        index_c1 += 1

    resolved_clause = ''

    if not complementary_check:
        return "NOT_COMPLEMENTARY"
    else:
        nr_of_literals = 0
        for literal in clause1:
            if nr_of_literals != 0:
                resolved_clause += ','
            resolved_clause += literal
            nr_of_literals += 1
        for literal in clause2:
            if literal not in clause1:
                if nr_of_literals != 0:
                    resolved_clause += ','
                resolved_clause += literal
                nr_of_literals += 1

    resolved_split = resolved_clause.split(',')
    index1 = 0

    # Ordering the new clause alphabetically to avoid adding copies of existing clauses
    while index1 < len(resolved_split):
        index2 = index1 + 1
        while index2 < len(resolved_split):
            if resolved_split[index1][0] == '!':
                str1 = resolved_split[index1][1:]
            else:
                str1 = resolved_split[index1]
            if resolved_split[index2][0] == '!':
                str2 = resolved_split[index2][1:]
            else:
                str2 = resolved_split[index2]
            if str1 > str2:
                aux = resolved_split[index1]
                resolved_split[index1] = resolved_split[index2]
                resolved_split[index2] = aux
            index2 = index2 + 1
        index1 = index1 + 1

    resolved_clause = ','.join(resolved_split)

    # Clause verification, if empty return tautology, if empty and both clauses only had one literal return unsat. if not
    # emtpy return the new clause
    if resolved_clause == '':
        if len(aux1) <= 2 and len(aux2) <= 2:
            return "UNSATISFIABLE"
        else:
            return "TAUTOLOGY"
    else:
        return resolved_clause
        # return new clause which is a concatenation of the input clauses without the complementary literals
        # or returns a code word in a string if both clauses had only one

def resolution():
    i = 0
    length = len(clause_list)
    while i < length:
        j = i + 1   # starts from i + 1 to not repeat already done resolving
        while j < length:
            if i != j:
                result = resolve(clause_list[i], clause_list[j])
                if result == 'NOT_COMPLEMENTARY':
                    # There are no complementary literals, don't resolve them
                    pass
                elif result == 'TAUTOLOGY':
                    # Resolving them results in a tautology, don't resolve them
                    pass
                elif result == 'UNSATISFIABLE':
                    # Results in an empty clause, stop the program and print UNSATISFIABLE
                    return "UNSATISFIABLE"
                else:
                    # only adds the clause if it wasn't in the list originally
                    if result not in clause_list:
                        clause_list.append(result)
                        # Check if the result is smaller than 2 in length, if yes apply one literal. Somehow get one
                        # literal to work with 1 argument it uses the one argument as the one literal?
                        if len(result) <= 2 and dp == 1:
                            output = OneLiteral()
                            if output =="SATISFIABLE":
                                return "SATISFIABLE"
                            elif output == "UNSATISFIABLE":
                                return "UNSATISFIABLE"
                        length = len(clause_list)
            j += 1
        i += 1
    return "SATISFIABLE"

def OneLiteral():
    global clause_list
    clause_double_list = list()
    return_value = 'ONE LITERAL APPLIED'

    length = len(clause_list)
    i = 0
    while i < length:
        literal_list = clause_list[i].split(',')
        clause_double_list.append(literal_list)
        i += 1

    single_literal = 'placeholder'
    length = len(clause_double_list)
    while single_literal != '':
        # allows to check if after applying the single literal rule there are new single literals created
        single_literal = ''
        i = 0
        while i < length:
            if single_literal != '':
                if single_literal[0] == '!':
                    # remove all the literals that have the single_literal without the ! from their clauses
                    # and remove all clauses that contain the entire single_literal
                    if single_literal in clause_double_list[i]:
                        clause_double_list.pop(i)
                        length -= 1
                        i -= 1
                    elif single_literal[1:] in clause_double_list[i]:
                        clause_double_list[i].remove(single_literal[1:])
                else:
                    # remove all complementary literals in their clauses, remove all clauses that contain the Single Literal
                    if single_literal in clause_double_list[i]:
                        clause_double_list.pop(i)
                        length -= 1
                        i -= 1
                    elif '!' + single_literal in clause_double_list[i]:
                        clause_double_list[i].remove('!' + single_literal)

                # Checks for SAT or UNSAT
                if len(clause_double_list) == 0:
                    # if there are no more clauses, return satisfiable
                    return_value = 'SATISFIABLE'
                    single_literal = ''
                    break
                elif len(clause_double_list[i]) == 0:
                    # if an empty clause is created after applying the one literal rule, then the entire problem is unsat
                    return_value = 'UNSATISFIABLE'
                    single_literal = ''
                    break
            elif len(clause_double_list[i]) == 1:
                # find the single literal, reset counter to 0 to check for the entire list
                single_literal += clause_double_list[i][0]
                i = -1
            i += 1
    # after all of this, need to update clause_list
    new_clause_list = list()
    for clause in clause_double_list:
        unsplit_clause = ""
        first_check = True

        for literal in clause:
            if not first_check:
                unsplit_clause += ','
            unsplit_clause += literal
            first_check = False
        new_clause_list.append(unsplit_clause)

    clause_list = new_clause_list
    return return_value

def PureLiteral():
    global clause_list

    str_all_literals = ','.join(clause_list)
    all_literal_list = str_all_literals.split(',')
    all_literal_set = set(all_literal_list)
    all_literal_list = list(all_literal_set)

    for literal in all_literal_list:
        if literal[0] == "!":
            if literal[1:] in all_literal_list:
                all_literal_list.remove(literal[1:])
                all_literal_list.remove(literal)
        else:
            if "!" + literal in all_literal_list:
                all_literal_list.remove(literal)
                all_literal_list.remove("!" + literal)

    # all_literal_list contains only the pure literals
    if len(all_literal_list) == 0:
       return "NO PURE LITERALS"

    clause_double_list = list()
    length = len(clause_list)
    i = 0
    while i < length:
        literal_list = clause_list[i].split(',')
        clause_double_list.append(literal_list)
        i += 1

    i = 0
    length2 = len(clause_double_list)
    for literal in clause_double_list[i]:
        if literal in all_literal_list:
            clause_double_list.pop(i)
            length2 -= 1
            i -= 1
    # clause_double_list contains the set of clauses after Pure Literal has been applied

    new_clause_list = list()
    for clause in clause_double_list:
        unsplit_clause = ""
        first_check = True
        for literal in clause:
            if not first_check:
                unsplit_clause += ','
            unsplit_clause += literal
            first_check = False
        new_clause_list.append(unsplit_clause)
    clause_list = new_clause_list
    if len(clause_list) == 0:
        return "SATISFIABLE"
    else:
        return "PURE LITERAL APPLIED"

def davis_putnam():
    # Repeats applying one literal then pure literal until both don't apply anymore
    ol_output = "placeholder"
    pl_output = 'placeholder'

    while ol_output != "ONE LITERAL APPLIED" and pl_output != "PURE LITERAL APPLIED":
        ol_output = OneLiteral()
        if ol_output == 'SATISFIABLE':
            return 'SATISFIABLE'
        elif ol_output == 'UNSATISFIABLE':
            return 'UNSATISFIABLE'
        pl_output = PureLiteral()
        if pl_output == 'SATISFIABLE':
            return 'SATISFIABLE'
    return resolution()

def main():
    global dp
    global clause_list

    og_input = str(input("Input set of clauses (must be formated like this:[A,B],[!A,C],[!A]): \n"))
    dp = input("Enable DP? 1 - yes / 0 - no \n")

    clause_list = clause_split1(og_input) # Splits the clauses into a list

    beginning = time.perf_counter()
    time.sleep(1)

    if dp == 1:
        output = davis_putnam()
        if output == "SATISFIABLE":
            print("SATISFIABLE")
        elif output == "UNSATISFIABLE":
            print("UNSATISFIABLE")
        else:
            print(output)
    else:
        print(resolution())

    end = time.perf_counter()
    print("Elapsed time: ", end - beginning)

main()
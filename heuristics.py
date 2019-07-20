#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented.

import random
'''
This file will contain different variable ordering heuristics to be used within
bt_search.

var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable 

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.

val_ordering == a function with the following template
    val_ordering(csp,var)
        ==> returns [Value, Value, Value...]
    
    csp is a CSP object, var is a Variable object; the heuristic can use csp to access the constraints of the problem, and use var to access var's potential values. 

    val_ordering returns a list of all var's potential values, ordered from best value choice to worst value choice according to the heuristic.

'''

def ord_mrv(csp):
    """

    :param csp: a csp that has unassigned variables
    :return: an unassigned variable of "csp" with least number of remaining values in its cur_dom
    """
    mrv = float('inf')
    next_var = None
    for unassigned_var in csp.get_all_unasgn_vars():
        if unassigned_var.cur_domain_size() < mrv:
            mrv = unassigned_var.cur_domain_size()
            next_var = unassigned_var
    return next_var


def merge(list1, list2):
    """

    :param list1: a sorted list
    :param list2: a sorted list
    :return: list1 and list2 combined in non-descending order
    """
    if len(list1) == 0:
        return list2
    if len(list2) == 0:
        return list1
    if list1[0][1] <= list2[0][1]:
        return [list1[0]] + merge(list1[1:], list2)
    else:
        return [list2[0]] + merge(list1, list2[1:])

def merge_sort(list):
    """

    :param list: an unsorted list
    :return: list sorted in non-decreasing order
    """
    if len(list) <= 1:
        return list
    else:
        mid = len(list)//2
        return merge(merge_sort(list[:mid]), merge_sort(list[mid:]))

def val_lcv(csp,input_var):
    """

    :param csp: a csp containing unassigned variables
    :param input_var: an unasigned variable in "csp"
    :return: a list of value in cur_dom of "input_var", sorted by the value that will be ruled out the in the remaining variables
    """
    involved_constraints = csp.get_cons_with_var(input_var)
    value_numPrune_tuples = []
    for input_var_value in input_var.cur_domain():
        sum_pruned = 0
        pruned = dict()
        for constraint in involved_constraints:
            involved_variables = constraint.get_scope()
            input_var_index = involved_variables.index(input_var)
            for i in range(len(involved_variables)):
                if i != input_var_index and not involved_variables[i].is_assigned():
                    cur_var = involved_variables[i]
                    if cur_var not in pruned.keys():
                        pruned[cur_var] = []
                    for cur_var_value in cur_var.cur_domain():
                        has_solution_before = constraint.has_support(cur_var, cur_var_value)
                        input_var.assign(input_var_value)
                        has_solution_after = constraint.has_support(cur_var, cur_var_value)
                        input_var.unassign()
                        if has_solution_before and not has_solution_after:
                            cur_var.prune_value(cur_var_value)
                            pruned[cur_var].append(cur_var_value)
                            sum_pruned += 1

        value_numPrune_tuples.append((input_var_value, sum_pruned))
        for pruned_var in pruned.keys():
            for pruned_value in pruned[pruned_var]:
                pruned_var.unprune_value(pruned_value)

    #sort the list of (inpt_var_value, num_total_pruned_value) tuples and return list of input_var_value,
    #in ascending order of num_total_pruned_value
    sorted = merge_sort(value_numPrune_tuples)
    return [item[0] for item in sorted]


if __name__ == '__main__':
    #test merger_sort()
    test_list = [("j", 10),("i", 9),("f", 6),("e", 5),("c", 3),("d", 4),("g", 7),("b", 2),("h",8),("a", 1)]
    sorted = merge_sort(test_list)
    res_lcv = [item[0] for item in sorted]
    print(res_lcv)

    # last_update: 2019-07-20 19:26


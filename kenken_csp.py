#Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects 
representing the board. The returned list of lists is used to access the 
solution. 

For example, after these three lines of code

    csp, var_array = kenken_csp_model(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the KenKen puzzle.

The grid-only models do not need to encode the cage constraints.

1. binary_ne_grid (worth 10/100 marks)
    - A model of a KenKen grid (without cage constraints) built using only 
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 10/100 marks)
    - A model of a KenKen grid (without cage constraints) built using only n-ary 
      all-different constraints for both the row and column constraints. 

3. kenken_csp_model (worth 20/100 marks) 
    - A model built using your choice of (1) binary binary not-equal, or (2) 
      n-ary all-different constraints for the grid.
    - Together with KenKen cage constraints.

'''
from cspbase import *
import itertools

def binary_ne_grid(kenken_grid):
    """

    :param kenken_grid: a list of list, first element being the size of the kenken grid board, rest are cage constraitns
    :return: the kenken csp and the kenken_grid board containing all variables
    """

    # size and variable domain of the board
    size = kenken_grid[0][0]
    var_dom = []
    for i in range(size):
        var_dom.append(i+1)
    all_Vars = []

    #initialize the board
    board = []
    for i in range(size):
        board.append([0]*size)

    #variables initialization, store each variable into its corresponding spot on the board
    #variables will be named after their coordinates, eg. V_11 = BOARD[0][0]
    for i in range(size):
        for j in range(size):
            var = Variable("Var_{}{}".format(i+1, j+1))
            var.add_domain_values(var_dom)
            board[i][j] = var
            all_Vars.append(var)

    #csp initialization using all variables
    kenken_csp = CSP("binary_kenken_csp", all_Vars)

    #binary-constraints initialization, from line to line
    satisfying_tuples = list(itertools.permutations(var_dom, 2))
    #row constraints
    for i in range(size):
        row_scope_pool = list(itertools.combinations(board[i], 2))
        for scope in row_scope_pool:
            row_constraint = Constraint("Row_Diff-({}, {})".format(scope[0].name, scope[1].name), scope)
            row_constraint.add_satisfying_tuples(satisfying_tuples)
            kenken_csp.add_constraint(row_constraint)

    #column constraints
    board_Transpose = []
    for i in range(size):
        board_Transpose.append([0]*size)
    for i in range(size):
        for j in range(size):
            board_Transpose[i][j] = board[j][i]
    for i in range(size):
        col_scope_pool = list(itertools.combinations(board_Transpose[i], 2))
        for scope in col_scope_pool:
            col_constraint = Constraint("Col_Diff-({}, {})".format(scope[0].name, scope[1].name), scope)
            col_constraint.add_satisfying_tuples(satisfying_tuples)
            kenken_csp.add_constraint(col_constraint)

    return kenken_csp, board


def nary_ad_grid(kenken_grid):
    """

    :param kenken_grid: a list of list, first element being the size of the kenken grid board, rest are cage constraitns
    :return: the kenken csp and the kenken_grid board containing all variables
    """

    # size and variable domain of the board
    size = kenken_grid[0][0]
    var_dom = []
    for i in range(size):
        var_dom.append(i + 1)
    all_Vars = []

    # initialize the board
    board = []
    for i in range(size):
        board.append([0] * size)

    # variables initialization, store each variable into its corresponding spot on the board
    # variables will be named after their coordinates, eg. V_11 = BOARD[0][0]
    for i in range(size):
        for j in range(size):
            var = Variable("Var_{}{}".format(i + 1, j + 1))
            var.add_domain_values(var_dom)
            board[i][j] = var
            all_Vars.append(var)

    #csp initialization
    kenken_csp = CSP("nary_kenken_csp", all_Vars)

    # binary-constraints initialization, from line to line
    satisfying_tuples = list(itertools.permutations(var_dom, size))
    # row constraints
    for i in range(size):
        row_constraint = Constraint("Row_Diff_{}".format(i+1), board[i])
        row_constraint.add_satisfying_tuples(satisfying_tuples)
        kenken_csp.add_constraint(row_constraint)

    # column constraints
    board_Transpose = []
    for i in range(size):
        board_Transpose.append([0]*size)
    for i in range(size):
        for j in range(size):
            board_Transpose[i][j] = board[j][i]
    for i in range(size):
        col_constraint = Constraint("Col_Diff_{}".format(i+1), board_Transpose[i])
        col_constraint.add_satisfying_tuples(satisfying_tuples)
        kenken_csp.add_constraint((col_constraint))

    return kenken_csp, board


def exist_satisfying_permutation(potential_sol, operation, expected_output):
    """

    :param potential_sol: an assignment for all variable in a particular cage constraint
    :param operation: 1: minus; 2: divide
    :param expected_output: expected output of the cage constraint
    :return: True if exist a permutation of variable assignment in "potential_sol" that can generate "expected_output"
             when combined using "operation"
    """
    permutation = list(potential_sol)
    all_possible_permutations = []
    for i in range(len(potential_sol)):
        temp = permutation[0]
        permutation[0] = permutation[i]
        permutation[i] = temp
        all_possible_permutations.append(tuple(permutation))

    for item in all_possible_permutations:
        real_output = item[0]
        counter = 1
        while counter < len(item):
            if operation == 1: #minus
                real_output -= item[counter]
            elif operation == 2: #divide
                real_output /= item[counter]
            else:
                print("operation is neither minus nor divide!\n")
                exit(200)
            counter += 1
        if real_output == expected_output:
            return True
    return False

def cage_constraint(board, cage, cage_index):
    """

    :param board: board[0][0] is the variable representing value of upper most cell
    :param cage: a list representing one cage constraint
    :param cage_index: index of the cage constraint this function returns
    :return: a cage constraint based on parameter "cage"
    """
    caged_variables = cage[0]
    operation = cage[1]
    expected_output = cage[2]
    size = len(board)
    var_dom = list(range(1,size+1))

    #the scope of the constraint
    scope = []
    for (row_index, col_index) in caged_variables:
        scope.append(board[row_index][col_index])

    #satisfying tuples for the constraint
    sat_tuples = []
    for potential_sol in itertools.product(var_dom, repeat=len(caged_variables)):
        real_output = potential_sol[0]
        counter = 1
        if operation == 0: #plus
            while counter < len(potential_sol):
                real_output += potential_sol[counter]
                counter += 1
        elif operation == 1 or operation == 2: #minus or divide
            if exist_satisfying_permutation(potential_sol, operation, expected_output):
                sat_tuples.append(potential_sol)
                continue
        elif operation == 3: #multiply
            while counter < len(potential_sol):
                real_output *= potential_sol[counter]
                counter += 1
        else:
            print("invalid operation!\n")
            exit(100)
        if real_output == expected_output:
            sat_tuples.append(potential_sol)

    #create the constraint
    constraint = Constraint("cage_constraint_No.{}".format(cage_index), scope)
    constraint.add_satisfying_tuples(sat_tuples)

    return constraint

def add_cageConstraints_to_model(csp_without_cages, board, all_cages):
    """

    :param csp_without_cages: kenken csp without cage constraints
    :param board: board[0][0] is the variable representing value of upper left cell
    :param all_cages: a list of lists, each element is a cage constraint
    :return: a kenken csp with all the cage constraint added
    """
    resulting_csp_after_adding_cage_constraints = csp_without_cages
    for i in range(len(all_cages)):
        cage = all_cages[i]
        cur_cage_constraint = cage_constraint(board, cage, i)
        resulting_csp_after_adding_cage_constraints.add_constraint(cur_cage_constraint)
    return resulting_csp_after_adding_cage_constraints

def kenken_csp_model(kenken_grid):
    """

    :param kenken_grid: a list of list, first element being the size of the kenken grid board, rest are cage constraitns
    :return: the kenken csp and the kenken_grid board containing all variables
    """

    #first build the n-nary grid csp model without cage constraints
    csp_without_cages, board = binary_ne_grid(kenken_grid)

    #extract the cage constraints info and store into a list, in the following form:
    #cages = [cage1: [[(var1_x, var1_y),(var2_x, var2_y),...], operation, result], cage2, cage3, ...]
    cages = []
    for i in range(1,len(kenken_grid)):
        cur_cage = kenken_grid[i]
        caged_variables = []
        for j in range(len(cur_cage)-2):
            caged_var = cur_cage[j]
            caged_var_coord = (caged_var//10-1, caged_var%10-1)
            caged_variables.append(caged_var_coord)
        cages.append([caged_variables, cur_cage[-1], cur_cage[-2]])

    #all all cage constraints
    return add_cageConstraints_to_model(csp_without_cages, board, cages), board



if __name__ == '__main__':
    #last update: 07-18 20:43

    # size = 5
    # board = []
    # for i in range(size):
    #     board.append([0]*size)
    # print(board)

    # dom = [1,2,3]
    # print(list(itertools.permutations(dom, 2)))


    # kenken_grid = [[3], [11, 21, 3, 0], [12, 22, 2, 1], [13, 23, 33, 6, 3], [31, 32, 5, 0]]
    # cages = []
    # for i in range(1,len(kenken_grid)):
    #     cur_cage = kenken_grid[i]
    #     caged_variables = []
    #     for j in range(len(cur_cage)-2):
    #         caged_var = cur_cage[j]
    #         caged_var_coord = (caged_var//10-1, caged_var%10-1)
    #         caged_variables.append(caged_var_coord)
    #     cages.append([caged_variables, cur_cage[-1], cur_cage[-2]])
    # print(cages)

    # list = []
    # for item in itertools.product([1,2,3], repeat=3):
    #     res = item[0]
    #     counter = 1
    #     while counter < len(item)-1:
    #         res *= item[counter]
    #         counter += 1
    #     res *= item[counter]
    #     # print(item)
    #     if res % 3 == 0:
    #         list.append(item)
    # print(list)

    # for i in itertools.permutations(list((1,2,2)), 3):
    #     print(i)

    # varDom = [1,2,3]
    # for item in list(itertools.product(varDom, repeat=3)):
    #     print(item)

    # board = [[1,2,3],[4,5,6],[7,8,9]]
    # board_T = []
    # for i in range(len(board)):
    #     board_T.append([0]*len(board[0]))
    # for i in range(len(board)):
    #     for j in range(len(board[0])):
    #         board_T[i][j] = board[j][i]
    #         print("board_T[{}][{}] = board[{}][{}] = {}".format(i,j,j,i,board[j][i]))
    #         print("\n")
    # print(board_T)

    # potential_sol = (1,2,3,4,5,6)
    # permutation = list(potential_sol)
    # all_possible_permutations = []
    # for i in range(len(potential_sol)):
    #     temp = permutation[0]
    #     permutation[0] = permutation[i]
    #     permutation[i] = temp
    #     all_possible_permutations.append(tuple(permutation))
    # print(all_possible_permutations)

    # test_csp, _ = binary_ne_grid([[2]])
    # for var in test_csp.get_all_vars():
    #     print("this var's name is: {}".format(var.name))

    var_dom = [1,2,3,4,5,6]
    for item in itertools.product(var_dom, repeat=len(var_dom)):
        print(item)
    pass

    #last_update: 2019-07-20 19:26
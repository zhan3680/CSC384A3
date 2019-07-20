#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.
'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

#prune all values in @last_var that violates @constraint, return True iff DWO happens
def FC_check(constraint, last_var):
    """

    :param constraint: constraint that has only one variable unassigned
    :param last_var: the last unassigned variable of "constraint"
    :return: True iff DWO happens; last_var after pruning; a list of (var, pruned_value) pairs
    """
    DWO = False
    last_var_after_prune = last_var
    pruned_values = []

    scope = constraint.get_scope()
    last_var_index = scope.index(last_var)
    assignment = []
    for i in range(len(scope)):
        if i == last_var_index:
            assignment.append(float('inf'))
        else:
            assignment.append(scope[i].get_assigned_value())
    for last_var_value in last_var.cur_domain():
        assignment[last_var_index] = last_var_value
        if not constraint.check(assignment):
            last_var_after_prune.prune_value(last_var_value)
            pruned_values.append((last_var_after_prune, last_var_value))

    if last_var_after_prune.cur_domain_size() == 0:
        DWO = True
    return (DWO, last_var_after_prune, pruned_values)

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
    DWO = False
    pruned_values = []

    if not newVar: #need to check all constraints that have one unassigned variable
        for con in csp.get_all_cons():
            if len(con.get_scope()) == 1:
                DWO, con.get_scope()[0], pruned_values_for_cur_con = FC_check(con, con.get_scope()[0])
                pruned_values.extend(pruned_values_for_cur_con)
                if DWO:
                    return (False, pruned_values)
    else: #only check those constraints with newVar in scope and one unassigned variable
        for con in csp.get_cons_with_var(newVar):
            if con.get_n_unasgn() == 1:
                DWO, con.get_unasgn_vars()[0], pruned_values_for_cur_con = FC_check(con, con.get_unasgn_vars()[0])
                pruned_values.extend(pruned_values_for_cur_con)
                if DWO:
                    return (False, pruned_values)

    return (True, pruned_values)

'''
This class obeys FIFO, but does not allow duplicate objects
'''
class UniqueQueue():
    def __init__(self):
        self.all_items = set()

    def put(self, item):
        self.all_items.add(item)

    def get(self):
        return self.all_items.pop()

    def empty(self):
        return len(self.all_items) == 0

def GAC_enforce(csp, input_GACQueue):
    """

    :param csp: the csp on which GAC algorithm is performed
    :param input_GACQueue: the UniqueQueue that containing all initial constraints for GAC
    :return: True iff DWO happens; a list of (var, pruned_value) pairs
    """
    GACQueue = input_GACQueue
    pruned = []
    while not GACQueue.empty():
        constraint = GACQueue.get()
        for var in constraint.get_scope():
            for value in var.cur_domain():
                if not constraint.has_support(var, value):
                    var.prune_value(value)
                    pruned.append((var, value))
                    if var.cur_domain_size() == 0:
                        # DWO = True
                        return True, pruned
                    else:
                        for con in csp.get_cons_with_var(var):
                            if con != constraint:
                                GACQueue.put(con)

    return False, pruned

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    GACQueue = UniqueQueue()
    if not newVar:
        for constraint in csp.get_all_cons():
            GACQueue.put(constraint)
    else:
        for related_constraint in csp.get_cons_with_var(newVar):
            GACQueue.put(related_constraint)

    DWO, pruned = GAC_enforce(csp, GACQueue)
    if DWO:
        return (False, pruned)
    else:
        return (True, pruned)

if __name__ == '__main__':
    #test UniqueQueue
    q = UniqueQueue()
    for i in range(10):
        q.put(2)
    for j in range(8):
        q.put(3)
    for k in range(18):
        q.put(2)
    sum = 0
    while not q.empty():
        print(q.get())
        sum += 1
    print("that is everything in the UniqueQueue!")

    if sum == 2:
        print("UniqueQueue worked!")
    else:
        print("test failed")
        print(sum)

    # last_update: 2019-07-20 19:26
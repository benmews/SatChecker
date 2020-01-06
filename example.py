import sys

def parse_dimacs(filename):
    clauses = []
    with open(sys.argv[1], 'r') as input_file:
        for line in input_file:
            if line[0] in ['c', 'p']:
                continue
            literals = list(map(int, line.split()))
            assert literals[-1] == 0
            literals = literals[:-1]
            clauses.append(literals)
    return clauses

def delete_doubles(clauses):
    for clause in clauses:
        for var in clause:
            if var*-1 in clause:
                clauses.remove(clause)
                break
    return clauses
    
def setup(clauses, activity_counter_setting):
    variable_set = []
    for clause in clauses:
        variable_set.extend(clause)
        variable_set =  [abs(ele) for ele in variable_set] 
        variable_set = list(set(variable_set))
    num_vars = len(variable_set)
    trail = []
    activities = {}
    watch = {}
    watched_variables = {}
    for var in variable_set:
        activities[var] = 0
        watch[var] = []
        watch[-var] = []
    activity_division_counter = activity_counter_setting
    for clause_index, clause in enumerate(clauses):
        watched_variables[clause_index] = []
        for var in clause[0:2]:
            watch, added, watched_variables = addToWatch(clause_index, clause, watch, trail, watched_variables)
    dat={}
    dat["clauses"] = clauses
    dat["watch"] = watch
    dat["trail"] = trail
    dat["activities"] = activities
    dat["watched_variables"] = watched_variables
    dat["num_vars"] = num_vars
    dat["variable_set"] = variable_set
    return variable_set, num_vars, trail, activities, watch, watched_variables, activity_division_counter

def increase_activities(conflict_parts, activities):
    for part in conflict_parts:
        var = part[0]
        if var < 0:var = var*-1
        activities[var] = activities[var]+1
    return activities

def addToWatch(clause_index, clause, watch, trail, watched_variables):
    vars_assigned = getAssignedVars(trail)
    vars_watched = watched_variables[clause_index]
    vars_open = [x for x in clause if x not in vars_watched]
    vars_open = [x for x in vars_open if x not in vars_assigned]
    if len(vars_open) == 0:
        return watch, "unsat", watched_variables
    var = vars_open[0]
    watch[var].append(clause_index)
    watched_variables[clause_index].append(var)
    print("trail: " + str(trail))
#    print("clause = " + str(clause))
#    print("assigned = "+str(vars_assigned))
#    print("vars watched = " + str(vars_watched))
#    print("vars open = " + str( vars_open))
#    print("watch:" +str(watch))
    return watch, "goon", watched_variables

def removeWatch(clauses, watch, trail, var, watched_variables):
    watch_this = watch[var].copy()
    print("trail= "+ str(trail))
#    print("watch_this: "+str(watch_this)+", var= " + str(var))
    for clause_index in watch_this:
        watch, added, watched_variables = addToWatch(clause_index, clauses[clause_index], watch, trail, watched_variables)
        watch[var].remove(clause_index)
        watched_variables[clause_index].remove(var)
    return watch, added, watched_variables

def getAssignedVars(trail):
    assigned = []
    for trai in trail:
        assigned.append(trai[0])
    return assigned

def getWatchedVars(watch, clause_index):
#    print("watch = " + str(watch) + " clause index = " + str(clause_index))
    variables = [var for var, cl_index in enumerate(watch) if cl_index == clause_index]
    return variables

def hasState(clauses, trail, watch): # not necessary bec of two watched lit scheme?
    sat_clauses_counter = 0
    for cl_index, clause in enumerate(clauses):
        state, var = checkState(clauses, trail, cl_index, clause)
        if state == "unsat":
            return "unsat", var, cl_index
        if state == "sat":
            sat_clauses_counter = sat_clauses_counter+1
        if state == 1:
            return "unit", var, cl_index
    if sat_clauses_counter == len(clauses):
        return "sat", var, cl_index
    return False, var, cl_index

def checkState(clauses, trail, cl_index, clause):
    assigned = getAssignedVars(trail)
    unsatisfied_vars = 0
    openvars = []
    for var in clause:
        if var*-1 in assigned:
            print("var = " + str(var) + ", assigned = " + str(assigned))
            unsatisfied_vars = unsatisfied_vars+1
        if var in assigned:
            return "sat", var
        if var not in assigned and var*-1 not in assigned:
            openvars.append(var)
    if unsatisfied_vars == len(clause):
        print("unsat here len clause = " + str(len(clause)) + ", unsatisfied_vars = " + str(unsatisfied_vars))
        return "unsat", clause[0]
    var = openvars[0]
    return len(clause)-unsatisfied_vars, var
            

def decide(clauses, trail, watch, activities, num_vars, variable_set, watched_variables):
    print("lentrail = "+ str(len(trail))+", numvars = " +str(num_vars))
    if len(trail) >= num_vars:
        return False, trail, watch, activities, watched_variables
    unassigned = [var for var in variable_set if var not in getAssignedVars(trail)]
    activities_unassigned = { key:value for key, value in activities.items() if key in unassigned}
    var = max(activities_unassigned)
    var = var*-1 # negative first
    trail.append([var, "DL"]) # var, DL or clause
    watch, added, watched_variables = removeWatch(clauses, watch, trail, var*-1, watched_variables)
    return True, trail, watch, activities, watched_variables
    
def backtrack(clauses, trail, watch, activities, watched_variables):
    print("backtrack")
    DL_or_cl = "start"
    conflict_parts = []
    while True:
        if len(trail) == 0:
            return clauses, trail, watch, activities, False
        var, DL_or_cl = trail[-1]
        del trail[-1]
        conflict_parts.append([var, DL_or_cl])
        if DL_or_cl == "DL": break;
    activities = increase_activities(conflict_parts, activities)  
    clauses, watch, watched_variables = add_conflict_clause(clauses, trail, watch, conflict_parts, watched_variables)     
    return clauses, trail, watch, activities, watched_variables, True

def add_conflict_clause(clauses, trail, watch, conflict_parts, watched_variables):
    conflict_clause = clauses[conflict_parts[0][1]].copy()
    for part in conflict_parts[1:-2]: # 0 is conflict variable, 1 is clause_index
        other_clause = clauses[part[1]].copy()
        if part[0] in conflict_clause:
            conflict_clause.remove(part[0])
            other_clause.remove(part[0]*-1)
        else:
            conflict_clause.remove(part[0]*-1)
            other_clause.remove(part[0])
        conflict_clause=list(set(conflict_clause+other_clause))
    clauses.append(conflict_clause)
    clause_index = len(clauses)
    watch, added, watched_variables = addToWatch(clause_index, conflict_clause, watch, trail, watched_variables)
    watch, added, watched_variables = addToWatch(clause_index, conflict_clause, watch, trail, watched_variables)
    return clauses, watch, watched_variables

def BCP(clauses, trail, watch, watched_variables):
    state, var, cl_index  = hasState(clauses, trail, watch)
    print("in BCP: state =" + str(state) + ", var = "+ str(var) + ", cl_index = " + str(cl_index))
    propagated = False
    while state == "unit":
        propagated == True
        trail.append([var, cl_index])
        state, var, cl_index = hasState(clauses, trail, watch)
        if state == "unsat" or state == "sat":
            return state, trail, watched_variables
        watch, added, watched_variables = removeWatch(clauses, watch, trail, var*-1, watched_variables)
        state, var, cl_index  = hasState(clauses, trail, watch)
    if hasState(clauses, trail, watch)[0] == "unsat"  or hasState(clauses, trail, watch)[0] == "sat":
        return state, trail, watched_variables
    return propagated, trail, watched_variables


def manage_activity_counter(activity_division_counter, variable_set, activity_counter_setting, activities):
    activity_division_counter = activity_division_counter-1
    if activity_division_counter == 0:
        for var in variable_set:
            activities[var] = activities[var]/2
        activity_division_counter = activity_counter_setting
    return activity_division_counter, activities


def DPLL(clauses, activity_counter_setting):
    variable_set, num_vars, trail, activities, watch, watched_variables, activity_division_counter = setup(clauses, activity_counter_setting)

    BCP_result, trail, watched_variables = BCP(clauses, trail, watch, watched_variables)
    if BCP_result == "unsat":return "unsat"

    while True:
        dec_false, trail, watch, activities, watched_variables= decide(clauses, trail, watch, activities, num_vars, variable_set, watched_variables)
        if not dec_false:return "sat"
        BCP_result, trail, watched_variables = BCP(clauses, trail, watch, watched_variables)
        if BCP_result == "sat":return "sat"
        while BCP_result == True:
            clauses, trail, watch, activities, watched_variables, has_backtracked = backtrack(clauses, trail, watch, activities, watched_variables)
            if not has_backtracked:return "unsat"
            BCP_result, trail, watched_variables = BCP(clauses, trail, watch, watched_variables)
            if BCP_result == "sat":return "sat"
            
        activity_division_counter, activities = manage_activity_counter(activity_division_counter, variable_set, activity_counter_setting, activities)

def run(file):
    result = DPLL(delete_doubles(parse_dimacs(file)), 100)
    if result == "unsat":print("unsat");sys.exit(20)
    else:print("sat");sys.exit(10)

run(sys.argv[1])

#print("after BCP. trail = " + str(trail))


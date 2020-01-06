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
    dat={}
    dat["clauses"] = clauses
    dat["watch"] = watch
    dat["trail"] = trail
    dat["activities"] = activities
    dat["watched_variables"] = watched_variables
    dat["num_vars"] = num_vars
    dat["variable_set"] = variable_set
    for clause_index, clause in enumerate(clauses):
        watched_variables[clause_index] = []
        for var in clause[0:2]:
            added = addToWatch(clause_index, clause, dat)
    
    return dat, activity_division_counter

def manage_activity_counter(activity_division_counter, activity_counter_setting, dat):
    activity_division_counter = activity_division_counter-1
    if activity_division_counter == 0:
        for var in dat["variable_set"]:
            dat["activities"][var] = dat["activities"][var]/2
        activity_division_counter = activity_counter_setting

def increase_activities(conflict_parts, dat):
    for part in conflict_parts:
        var = part[0]
        if var < 0:var = var*-1
        dat["activities"][var] = dat["activities"][var]+1

def addToWatch(clause_index, clause, dat):
    vars_assigned = getAssignedVars(dat)
    vars_watched = dat["watched_variables"][clause_index]
    vars_open = [x for x in clause if x not in vars_watched]
    vars_open = [x for x in vars_open if x not in vars_assigned]
    if len(vars_open) == 0:
        return "unsat"
    var = vars_open[0]
    dat["watch"][var].append(clause_index)
    dat["watched_variables"][clause_index].append(var)
    print("trail: " + str(dat["trail"]))
#    print("clause = " + str(clause))
#    print("assigned = "+str(vars_assigned))
#    print("vars watched = " + str(vars_watched))
#    print("vars open = " + str( vars_open))
#    print("watch:" +str(watch))
    return "goon"

def removeWatch(dat, var):
    watch_this = dat["watch"][var].copy()
    print("trail= "+ str(dat["trail"]))
#    print("watch_this: "+str(watch_this)+", var= " + str(var))
    for clause_index in watch_this:
        added = addToWatch(clause_index, dat["clauses"][clause_index], dat)
        dat["watch"][var].remove(clause_index)
        dat["watched_variables"][clause_index].remove(var)
    return added

def getAssignedVars(dat):
    assigned = []
    for trai in dat["trail"]:
        assigned.append(trai[0])
    return assigned

def getWatchedVars(watch, clause_index):
#    print("watch = " + str(watch) + " clause index = " + str(clause_index))
    variables = [var for var, cl_index in enumerate(watch) if cl_index == clause_index]
    return variables

def hasState(dat): # not necessary bec of two watched lit scheme?
    sat_clauses_counter = 0
    for cl_index, clause in enumerate(dat["clauses"]):
        state, var = checkState(dat, cl_index, clause)
        if state == "unsat":
            return "unsat", var, cl_index
        if state == "sat":
            sat_clauses_counter = sat_clauses_counter+1
        if state == 1:
            return "unit", var, cl_index
    if sat_clauses_counter == len(dat["clauses"]):
        return "sat", var, cl_index
    return False, var, cl_index

def checkState(dat, cl_index, clause):
    assigned = getAssignedVars(dat)
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
            

def decide(dat):
    print("lentrail = "+ str(len(dat["trail"]))+", numvars = " +str(dat["num_vars"]))
    if len(dat["trail"]) >= dat["num_vars"]:
        return False
    unassigned = [var for var in dat["variable_set"] if var not in getAssignedVars(dat)]
    activities_unassigned = { key:value for key, value in dat["activities"].items() if key in unassigned}
    var = max(activities_unassigned)
    var = var*-1 # negative first
    dat["trail"].append([var, "DL"]) # var, DL or clause
    added = removeWatch(dat, var*-1)
    return True
    
def backtrack(dat):
    print("backtrack")
    DL_or_cl = "start"
    conflict_parts = []
    while True:
        if len(dat["trail"]) == 0:
            return False
        var, DL_or_cl = dat["trail"][-1]
        del dat["trail"][-1]
        conflict_parts.append([var, DL_or_cl])
        if DL_or_cl == "DL": break;
    increase_activities(conflict_parts, dat)  
    add_conflict_clause(dat, conflict_parts)     
    return True

def add_conflict_clause(dat, conflict_parts):
    conflict_clause = dat["clauses"][conflict_parts[0][1]].copy()
    for part in conflict_parts[1:-2]: # 0 is conflict variable, 1 is clause_index
        other_clause = dat["clauses"][part[1]].copy()
        if part[0] in conflict_clause:
            conflict_clause.remove(part[0])
            other_clause.remove(part[0]*-1)
        else:
            conflict_clause.remove(part[0]*-1)
            other_clause.remove(part[0])
        conflict_clause=list(set(conflict_clause+other_clause))
    dat["clauses"].append(conflict_clause)
    clause_index = len(dat["clauses"])
    added = addToWatch(clause_index, conflict_clause, dat)
    added = addToWatch(clause_index, conflict_clause, dat)

def BCP(dat):
    state, var, cl_index  = hasState(dat)
    print("in BCP: state =" + str(state) + ", var = "+ str(var) + ", cl_index = " + str(cl_index))
    propagated = False
    while state == "unit":
        propagated == True
        dat["trail"].append([var, cl_index])
        state, var, cl_index = hasState(dat)
        if state == "unsat" or state == "sat":
            return state
        added = removeWatch(dat, var*-1)
        state, var, cl_index  = hasState(dat)
    if hasState(dat)[0] == "unsat"  or hasState(dat)[0] == "sat":
        return state
    return propagated


def DPLL(clauses, activity_counter_setting):
    dat, activity_division_counter = setup(clauses, activity_counter_setting)

    BCP_result = BCP(dat)
    if BCP_result == "unsat":return "unsat"

    while True:
        dec_false = decide(dat)
        if not dec_false:return "sat"
        BCP_result = BCP(dat)
        if BCP_result == "sat":return "sat"
        while BCP_result == True:
            has_backtracked = backtrack(dat)
            if not has_backtracked:return "unsat"
            BCP_result = BCP(dat)
            if BCP_result == "sat":return "sat"
            
        manage_activity_counter(activity_division_counter, activity_counter_setting, dat)

def run(file):
    result = DPLL(delete_doubles(parse_dimacs(file)), 100)
    if result == "unsat":print("unsat");sys.exit(20)
    else:print("sat");sys.exit(10)

run(sys.argv[1])

#print("after BCP. trail = " + str(trail))


from cfmtoolbox import app, CFM, Feature
from cfmtoolbox_csp_encoder.cloningCSP import create_csp_cloning_encoding, \
    create_amount_of_children_for_group_instance_cardinality_cloning_csp, getMaxCardinality
from cfmtoolbox_ilp_encoder import get_max_interval_value
from ortools.sat.python import cp_model
from cfmtoolbox_csp_encoder.multisetCSP import (create_multiset_csp_encoding, create_const_name,
                                                get_variables, variables)
from ortools.sat.python.cp_model import CpModel


@app.command()
def run_csp_solver_cloning(cfm: CFM):
    model = create_csp_cloning_encoding(cfm,True)
    model.ExportToFile('raw_model.txt')

@app.command()
def run_csp_solver_cloning_maximize_basis(cfm: CFM):
    model = create_csp_cloning_encoding(cfm,True)

    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    maximize_or_minimize(model,cfm.root,True,cfm.root,[],True)


def maximize_or_minimize(model: CpModel, feature: Feature,maximize: bool,root: Feature, parent_list: list[int],only_boolean_constants: bool):

    if maximize:
        model.maximize(sum(create_amount_of_children_for_group_instance_cardinality_cloning_csp([feature], parent_list, only_boolean_constants)))

    solver = cp_model.CpSolver()
    status = solver.solve(model)

    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        print(feature.name + ": " + str(solver.objective_value))
        if solver.objective_value < get_max_interval_value(feature.instance_cardinality.intervals):
            print(feature.name + ": ")
            print("Given feature instance cardinality: " + str(get_max_interval_value(
                feature.instance_cardinality.intervals)) + "\n")
            print("Actual Max Feature Instance Cardinality " + str(solver.objective_value) + "\n")


    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for children in feature.children:
        old_list = parent_list.copy()
        maximize_or_minimize(model, children, maximize, root, old_list,
                                        only_boolean_constants)





@app.command()
def run_csp_solver_maximize_cardinalities(cfm: CFM):
    model = create_multiset_csp_encoding(cfm)

    variables = get_variables()
    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    solver = cp_model.CpSolver()
    status = solver.solve(model)


    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        for key in variables:
           print(key + ": " + str(solver.Value(variables[key])))

    find_actual_max(model,cfm.root,1)



def find_actual_max(model, feature: Feature, max_parent_cardinality: int):
    variables = get_variables()


    model.maximize(variables[create_const_name(feature)])
    model.ExportToFile('raw_model.txt')




    solver = cp_model.CpSolver()
   # solver.parameters.log_search_progress = True
   # solver.parameters.cp_model_probing_level = 0  # Enable presolve (default)
   # solver.parameters.cp_model_presolve = True
    #solver.parameters.num_search_workers = 1  # Single-threaded for deterministic debugging
    status = solver.solve(model)




    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        #print(solver.objective_value)
        if int(solver.objective_value) > 1:
            actual_max = int(solver.objective_value) / max_parent_cardinality
            new_max = round(max_parent_cardinality * actual_max, None)
        else:
            actual_max = int(solver.objective_value)
            new_max = max_parent_cardinality
        if actual_max < get_max_interval_value(feature.instance_cardinality.intervals):
            print(feature.name + ": ")
            print("Given feature instance cardinality: " + str(get_max_interval_value(
                feature.instance_cardinality.intervals)) + "\n")
            print("Actual Max Feature Instance Cardinality " + str(round(actual_max, None)) + "\n")
        #for key in variables:
        #    print(key + ": " + str(solver.Value(variables[key])))
    else:
        print("No solution found.")
        new_max = 0


    '''
    print("\nStatistics")
    print(f"  status   : {solver.status_name(status)}")
    print(f"  conflicts: {solver.num_conflicts}")
    print(f"  branches : {solver.num_branches}")
    print(f"  wall time: {solver.wall_time} s")
    '''
    for child in feature.children:
        find_actual_max(model, child, new_max)


    #        for variable in solver.variables():
       #     print(f"{variable.name()} = {variable.solution_value()}")

@app.command()
def run_csp_basis_gap_detection(cfm: CFM):

    model = create_csp_cloning_encoding(cfm,True)

    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    return find_gaps_in_all_clones(cfm.root,model,[],True)


@app.command()
def run_csp_with_integer_leaves_gap_detection(cfm: CFM):

    model = create_csp_cloning_encoding(cfm,False)
    model.ExportToFile('raw_model.txt')
    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    return find_gaps_in_all_clones(cfm.root,model,[],False)


def find_gaps_in_all_clones(feature: Feature, model: CpModel, parent_list: list[int],
                            only_boolean_constants: bool):
    gaps = ""

    print(feature.name)

    for interval in feature.instance_cardinality.intervals:

        for j in range(interval.lower, interval.upper + 1):
            new_model = model.clone()
            sum_variables = create_amount_of_children_for_group_instance_cardinality_cloning_csp(
                [feature], parent_list, only_boolean_constants=only_boolean_constants)
            new_model.add(sum(sum_variables) == j)

            solver = cp_model.CpSolver()
            # solver.parameters.log_search_progress = True
            # solver.parameters.cp_model_probing_level = 0  # Enable presolve (default)
            # solver.parameters.cp_model_presolve = True
            # solver.parameters.num_search_workers = 1  # Single-threaded for deterministic debugging
            status = solver.solve(new_model)
            if status == cp_model.INFEASIBLE:
                gap = "Gap at: " + str(j) + " in Feature: " + feature.name + " "
                print(gap)
                gaps += gap

    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        gaps += find_gaps_in_all_clones(feature, model, old_list, only_boolean_constants)
    return gaps

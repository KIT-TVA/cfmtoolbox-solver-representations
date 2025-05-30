import re

from cfmtoolbox import app, CFM, Feature
from cfmtoolbox_csp_encoder.cloningCSP import create_csp_cloning_encoding, \
    create_amount_of_children_for_group_instance_cardinality_cloning_csp, getMaxCardinality, \
    get_all_cloned_variables, get_all_clones_of_feature, add_constraint_to_remove_permutations, \
    getMinCardinality
from cfmtoolbox_smt_encoder import get_min_cardinality
from ortools.sat.python import cp_model
from cfmtoolbox_csp_encoder.multisetCSP import (create_multiset_csp_encoding, create_const_name,
                                                get_variables, variables, get_max_interval_value,
                                                get_min_interval_value)
from ortools.sat.python.cp_model import CpModel


@app.command()
def run_csp_solver_cloning(cfm: CFM):
    model = create_csp_cloning_encoding(cfm,True)
    model.ExportToFile('raw_model.txt')

@app.command()
def get_csp_multiset_stats(cfm: CFM):
    model = create_multiset_csp_encoding(cfm,False)
    print_model_stats(model)

@app.command()
def get_csp_cloning_basis_stats(cfm: CFM):
    model = create_csp_cloning_encoding(cfm,True)
    print_model_stats(model)

@app.command()
def get_csp_cloning_integer_leaves_stats(cfm: CFM):
    model = create_csp_cloning_encoding(cfm,False)
    print_model_stats(model)


def print_model_stats(model):
    proto = model.Proto()
    print(f"Model statistics:")
    print(f"- Variables: {len(proto.variables)}")
    print(f"- Constraints: {len(proto.constraints)}")


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
        #print(feature.name + ": " + str(solver.objective_value))
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
    model = create_multiset_csp_encoding(cfm, False)

    variables = get_variables()
    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    """
    solver = cp_model.CpSolver()
    status = solver.solve(model)

   
    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        for key in variables:
           print(key + ": " + str(solver.Value(variables[key])))
    """
    find_actual_max(model,cfm.root,1,cfm.features)

@app.command()
def run_csp_multiset_bound_analysis(cfm: CFM):
    model = create_multiset_csp_encoding(cfm,True)
    variables = get_variables()
    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    find_actual_min(model,cfm.root,cfm.features,1)
    model = create_multiset_csp_encoding(cfm, False)
    find_actual_max(model,cfm.root,1,cfm.features)



def find_actual_max(model, feature: Feature, max_parent_cardinality: int, features):
    variables = get_variables()

    model.maximize(variables[create_const_name(feature)])
    model.ExportToFile('raw_model.txt')




    solver = cp_model.CpSolver()
    status = solver.solve(model)
   # solver.parameters.log_search_progress = True
   # solver.parameters.cp_model_probing_level = 0  # Enable presolve (default)
   # solver.parameters.cp_model_presolve = True
    #solver.parameters.num_search_workers = 1  # Single-threaded for deterministic debugging

    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        """for value in features:
            sample_variable = variables[create_const_name(value)]
            print(f"{value.name}={solver.Value(sample_variable)}", end=" \n")
        print(solver.objective_value)"""
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


    for child in feature.children:
       # new_max = new_max if new_max != 0 else 1
        find_actual_max(model, child, new_max, features)

    '''
    print("\nStatistics")
    print(f"  status   : {solver.status_name(status)}")
    print(f"  conflicts: {solver.num_conflicts}")
    print(f"  branches : {solver.num_branches}")
    print(f"  wall time: {solver.wall_time} s")
    '''


def find_actual_min(model, feature: Feature, features, min_parent_cardinality: int):
    variables = get_variables()

    model.minimize(variables[create_const_name(feature)])
    model.ExportToFile('raw_model.txt')

    solver = cp_model.CpSolver()
    status = solver.solve(model)
    # solver.parameters.log_search_progress = True
    # solver.parameters.cp_model_probing_level = 0  # Enable presolve (default)
    # solver.parameters.cp_model_presolve = True
    # solver.parameters.num_search_workers = 1  # Single-threaded for deterministic debugging

    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        """for value in features:
            sample_variable = variables[create_const_name(value)]
            print(f"{value.name}={solver.Value(sample_variable)}", end=" \n")
        print(solver.objective_value)"""
        if solver.objective_value > 1:
            actual_min = int(solver.objective_value) / min_parent_cardinality
            actual_min = round(actual_min)
            min_parent_cardinality = round(min_parent_cardinality * actual_min, None)
        else:
            actual_min = solver.objective_value

        if actual_min > get_min_interval_value(
                feature.instance_cardinality.intervals):
            print(feature.name + ": ")
            print("Given feature instance cardinality: " + str(get_min_interval_value(
                feature.instance_cardinality.intervals)) + "\n")
            print("Actual Min Feature Instance Cardinality " + str(round(actual_min)) + "\n")
        # for key in variables:
        #    print(key + ": " + str(solver.Value(variables[key])))
    else:
        print("No solution found.")


    for child in feature.children:

        find_actual_min(model, child, features, min_parent_cardinality)


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
    add_constraint_to_remove_permutations(model, cfm.root, [],
                                          only_boolean_constants=False)
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
        min_cardinality = getMinCardinality(feature.instance_cardinality.intervals) if (
            getMinCardinality(feature.instance_cardinality.intervals)) > 0 else 1
        parent_list.append(min_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        gaps += find_gaps_in_all_clones(feature, model, old_list, only_boolean_constants)
    return gaps


@app.command()
def run_csp_cloning_basis_sampling(cfm: CFM):
    model = create_csp_cloning_encoding(cfm,True)
    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    solver = cp_model.CpSolver()
    solution_printer = VarSolutionPrinter(get_all_cloned_variables())
    solver.parameters.enumerate_all_solutions = True
    status = solver.solve(model,solution_printer)

    print(f"Number of solutions found: {solution_printer.solution_count}")


@app.command()
def run_csp_cloning_with_integer_leaves_sampling(cfm: CFM):
    model = create_csp_cloning_encoding(cfm,False)
    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    solver = cp_model.CpSolver()
    solution_printer = VarSolutionPrinter(get_all_cloned_variables())
    solver.parameters.enumerate_all_solutions = True
    status = solver.solve(model,solution_printer)

    print(f"Number of solutions found: {solution_printer.solution_count}")


@app.command()
def run_csp_cloning_with_integer_leaves_sampling_without_permutation(cfm: CFM):
    model = create_csp_cloning_encoding(cfm,False)
    add_constraint_to_remove_permutations(model, cfm.root, [],
                                          only_boolean_constants=False)

    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    solver = cp_model.CpSolver()
    solution_printer = VarSolutionPrinter(get_all_cloned_variables())
    solver.parameters.enumerate_all_solutions = True
    status = solver.solve(model,solution_printer)

    print(f"Number of solutions found: {solution_printer.solution_count}")


@app.command()
def run_csp_multiset_with_cloning_sampling(cfm: CFM):
    model = create_multiset_csp_encoding(cfm, False)
    cloning_model = create_csp_cloning_encoding(cfm, False)
    try:
        model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    solver = cp_model.CpSolver()
    solution_printer = VarMultisetSolutionPrinter(get_variables(),cfm,cloning_model)
    solver.parameters.enumerate_all_solutions = True
    status = solver.solve(model,solution_printer)

    print(f"Number of solutions found: {solution_printer.solution_count} with "
          f"{solution_printer.multiset_samples}  Multiset "
          f"Samples")



def call_cloning_solver_with_multiset_sample(multi_set_sample,cfm,cloningModelIn):
    cloning_model = cloningModelIn.clone()

    for name,value in multi_set_sample.items():
        #print(value)
        cloning_model.add(sum(get_all_clones_of_feature(name)) == value)
        #print(get_all_clones_of_feature(name))
    try:
        cloning_model.Validate()
        print("Model is valid.")
    except Exception as e:
        print(f"Model validation failed: {e}")

    solver = cp_model.CpSolver()
    status = solver.solve(cloning_model)

    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        """
        for v in get_all_cloned_variables():
            print(f"{v.name}={solver.value(v)}", end=" ")
        """
    return status


class VarSolutionPrinter(cp_model.CpSolverSolutionCallback):
    """Print intermediate solutions."""

    def __init__(self, variables: list[cp_model.IntVar]):
        cp_model.CpSolverSolutionCallback.__init__(self)
        self.__variables = variables
        self.__solution_count = 0


    def on_solution_callback(self) -> None:
        self.__solution_count += 1
        """
        for v in self.__variables:
            print(f"{v}={self.value(v)}", end=" ")
        """
        print(f"Solution -> {self.__solution_count}",end="\n")
        print()

    @property
    def solution_count(self) -> int:
        return self.__solution_count

class VarMultisetSolutionPrinter(cp_model.CpSolverSolutionCallback):
    """Print intermediate solutions."""

    def __init__(self, variables,cfm:CFM,cloningModelIn):
        cp_model.CpSolverSolutionCallback.__init__(self)
        self.__variables = variables
        self.__solution_count = 0
        self.__multiset_samples = 0
        self.cfm = cfm
        self.cloningModelIn = cloningModelIn

    def on_solution_callback(self) -> None:
        multiset_sample = {}
        """
        for variable in self.__variables.values():
            print(f"{variable}={self.value(variable)}", end=" \n")
        """
        for feature in self.cfm.features:
            sample_variable = self.__variables[create_const_name(feature)]
            multiset_sample[feature.name] = self.value(sample_variable)
            print(f"{feature.name}={self.value(sample_variable)}", end=" \n")
        #print(f"Multiset -> {multiset_sample}",end="\n")
        self.__multiset_samples += 1
        status = call_cloning_solver_with_multiset_sample(multiset_sample, self.cfm,self.cloningModelIn)
        if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
            self.__solution_count += 1
            print(f"Solution -> {self.__solution_count}: Multiset Sample -> "
                  f"{self.__multiset_samples}",
                  end="\n")
        else:
            print(f"no valid configuration for this multiset representation")
        print()


    @property
    def solution_count(self) -> int:
        return self.__solution_count

    @property
    def multiset_samples(self) -> int:
        return self.__multiset_samples




from cfmtoolbox import CFM, Feature, Interval, Constraint




def create_smt_multiset_encoding(cfm: CFM):
    print("Encoding CFM...")
    encoding = ""

    encoding += declare_constants(cfm.features)
    encoding += create_assert_child_parent_connection(cfm.root.children)
    encoding += create_assert_feature_group_type_cardinality(cfm.root)
    encoding += create_assert_feature_group_instance_cardinality(cfm.root)
    encoding += create_assert_feature_instance_cardinality(cfm.root, [Interval(1, 1)])
    encoding += create_assert_constraints(cfm.constraints)

    print(encoding)
    return encoding


def create_assert_feature_group_type_cardinality(feature: Feature):
    assertStatement = ""
    if feature.group_type_cardinality.intervals:
        assertStatement += "(assert "
        if len(feature.group_type_cardinality.intervals) > 1:
            assertStatement += "(or"
        for interval in feature.group_type_cardinality.intervals:

            assertStatement += "(and "
            assertStatement += "(>= "
            assertStatement += create_amount_of_children_for_group_type_cardinality(feature.children, feature)
            assertStatement += str(interval.lower)
            assertStatement += ")"
            if interval.upper is None:
                assertStatement += "(= true true)"
            else:
                assertStatement += "(<= "
                assertStatement += create_amount_of_children_for_group_type_cardinality(feature.children, feature)
                assertStatement += str(interval.upper)
                assertStatement += ")"
            assertStatement += ")"  # closing and
        if len(feature.group_type_cardinality.intervals) > 1:
            assertStatement += ")"  # closing or
        assertStatement += ")\n"  # closing assert

    for child in feature.children:
        assertStatement += create_assert_feature_group_type_cardinality(child)
    return assertStatement




def create_assert_constraints(constraints):
    assertStatement = ""
    for constraint in constraints:
        assertStatement += "(assert "
        assertStatement += "(ite "
        assertStatement += create_constraint_feature_to_intervals(constraint.first_cardinality.intervals, constraint.first_feature)
        if not constraint.require:
            assertStatement += "(not "

        assertStatement += create_constraint_feature_to_intervals(constraint.second_cardinality.intervals, constraint.second_feature)

        if not constraint.require:
            assertStatement += " )" # closing not

        assertStatement += "(= true true)"
        assertStatement += ")" #closing ite
        assertStatement += ")\n" # closing assert
    return assertStatement


def create_constraint_feature_to_intervals(intervals: list, feature: Feature):
    constraint = ""
    if len(intervals) > 1:
        constraint +=  "(or "
    for interval in intervals:
        constraint = "(and "
        constraint += "(<= "
        constraint += create_const_name(feature)
        constraint += " "
        constraint += str(interval.upper)
        constraint += ")"
        constraint += "(>= "
        constraint += create_const_name(feature)
        constraint +=  " "
        constraint += str(interval.lower)
        constraint += ")"
        constraint += ")" # closing and
    if len(intervals) > 1:
        constraint += ")" #closing or
    return constraint

def create_assert_feature_instance_cardinality(feature: Feature, parent_intervals: list[Interval]):
    assert_statement = ""
    new_parent_intervals = parent_intervals.copy()
    assert_statement += "(assert "
    if len(parent_intervals) > 1:
        assert_statement += "(or"
    for parentInterval in parent_intervals:
        if len(feature.instance_cardinality.intervals) > 1:
            assert_statement += "(or"
        for interval in feature.instance_cardinality.intervals:
            assert_statement += "(and "
            assert_statement += "(>= "
            assert_statement += create_const_name(feature) + " "
            assert_statement += str(interval.lower * parentInterval.lower)
            assert_statement += ") "
            assert_statement += "(<= "
            assert_statement += create_const_name(feature) + " "
            assert_statement += str(interval.upper *  parentInterval.upper)
            assert_statement += ") "
            assert_statement += ")" # closing and

        if len(feature.instance_cardinality.intervals) > 1:
            assert_statement += ")"  # closing or
    if len(parent_intervals) > 1:
        assert_statement += ")"
    assert_statement += ")\n" # closing assert

    new_intervals =  add_new_parent_interval_to_intervals(new_parent_intervals, feature.instance_cardinality.intervals)

    for child in feature.children:
        assert_statement += create_assert_feature_instance_cardinality(child, new_intervals)

    return assert_statement

def add_new_parent_interval_to_intervals(parentIntervals: list[Interval], newIntervals: list[Interval]):
    output_list = []
    for interval in parentIntervals:
        for newInterval in newIntervals:
            output_list.append(Interval(interval.lower * newInterval.lower,interval.upper * newInterval.upper))

    return output_list


def create_amount_of_children_for_group_type_cardinality(features: list, parent: Feature):
    amount = ""

    amount += "(+ "
    for feature in features:
        amount += "(ite "
        amount += "(>= " + create_const_name(feature) + " "
        amount += create_const_name(parent) # for group type cardinality in multisets, it is only valid if the feature is in all subtrees -> if the lower and upper bound are equal this is necessary
        amount +=  ")"                       # for max bounded check this should not change anything
        amount += " 1 "
        amount += " 0 "
        amount += " )" # closing ite
    amount += " )" # closing +

    return amount


def create_sum_of_children_for_group_type_cardinality(features: list):
    sum = ""

    sum += "(+ "
    for feature in features:
        sum += create_const_name(feature)
        sum += " "
    sum += " )" # closing +

    return sum


def create_assert_feature_group_instance_cardinality(feature: Feature):
    assert_statement = ""
    if feature.group_instance_cardinality.intervals:
        assert_statement += "(assert "

        if len(feature.group_instance_cardinality.intervals) > 1:
            assert_statement += "(or"
        for interval in feature.group_instance_cardinality.intervals:
            assert_statement += "(and "
            assert_statement += "(>= "
            assert_statement += create_sum_of_children_for_group_type_cardinality(feature.children)
            assert_statement += " "

            assert_statement += "(* " + str(interval.lower) + " " +  create_const_name(feature) + ")"   #str(interval.lower * parentInterval.lower)

            assert_statement += ") "
            assert_statement += "(<= "
            assert_statement += create_sum_of_children_for_group_type_cardinality(feature.children)
            assert_statement += " "

            assert_statement += "(* " + str(interval.upper) + " " + create_const_name(feature) + ")"  # str(interval.upper * parentInterval.upper)
            assert_statement += ") "
            assert_statement += ")" # closing and

        if len(feature.group_instance_cardinality.intervals) > 1:
            assert_statement += ")"  # closing or
        assert_statement += ")\n" # closing assert

    for child in feature.children:
        assert_statement += create_assert_feature_group_instance_cardinality(child)

    return assert_statement


def create_assert_child_parent_connection(features: list) -> str:
    childrenAssert = ""

    if len(features) != 0:
        if features.__getitem__(0).parent.parent is None:
            childrenAssert += "(assert "
            childrenAssert += "(and "
            for feature in features:
                childrenAssert += create_assert_child_parent_connection(feature.children)

            childrenAssert += " )" # closing and
        else:
            childrenAssert += "(and "
            for feature in features:
                childrenAssert += "(ite "
                childrenAssert += "(= " + create_const_name(feature.parent) + " 0)"
                childrenAssert += "(= " + create_const_name(feature) + " 0)"
                childrenAssert += "(>= " + create_const_name(feature) + " 0)"
                childrenAssert += ")" # closing ite
                childrenAssert += create_assert_child_parent_connection(feature.children)
            childrenAssert += " )" #closind and

    if len(features) != 0:
        if features.__getitem__(0).parent.parent is None:
            childrenAssert += " )\n" # closing assert

    return childrenAssert


def declare_constants(features: list) -> str:
    constants = ""

    for feature in features:
        constants += "(declare-const " + create_const_name(feature) + " Int)\n"

    return constants


def get_all_constants_of_CFM_mulitset(cfm: CFM):
    constant_list = []
    for feature in cfm.features:
        constant_list.append(create_const_name(feature))
    return constant_list

def create_const_name(feature: Feature) -> str:
    return "Feature_" + feature.name

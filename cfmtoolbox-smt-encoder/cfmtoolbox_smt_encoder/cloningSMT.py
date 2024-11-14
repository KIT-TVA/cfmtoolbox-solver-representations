from cfmtoolbox import CFM, Feature, Interval

from cfmtoolbox_smt_encoder.mulitsetSMT import create_const_name




def create_smt_cloning_encoding(cfm: CFM):
    print("Encoding CFM...")
    encoding = ""

    encoding += declare_cloned_constants(cfm.root,1)

    print(encoding)
    return encoding


def declare_cloned_constants(parent: Feature, parentMaxCardinality: int):
    constants = ""
    max = 1;
    for i in range(parentMaxCardinality):
        constants += "(declare-const " + create_const_name(parent) + "_" + str(i) + " Bool)\n"
    for intervals in parent.instance_cardinality.intervals:
        for interval in intervals:
            if interval.upper >= max:
                max = interval.upper

    for feature in parent.children:
        constants += declare_cloned_constants(feature, max)

    return constants


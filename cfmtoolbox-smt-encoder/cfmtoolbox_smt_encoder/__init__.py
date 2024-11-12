
from cfmtoolbox import app, CFM
from cfmtoolbox_smt_encoder.mulitsetSMT import create_smt_multiset_encoding


@app.command()
def encode_to_smt_multiset(cfm: CFM) -> str:
    encoding = create_smt_multiset_encoding(cfm)
    return encoding


@app.command()
def encode_to_smt_cloning(cfm: CFM) -> str:
    print("Encoding CFM...")
    encoding = ""


    print(encoding)
    return encoding




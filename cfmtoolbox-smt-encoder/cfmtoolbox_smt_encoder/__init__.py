import os
import sys

from cfmtoolbox import app, CFM
from cfmtoolbox_smt_encoder.mulitsetSMT import create_smt_multiset_encoding
import subprocess




@app.command()
def encode_to_smt_multiset(cfm: CFM) -> str:
    encoding = create_smt_multiset_encoding(cfm)
    return encoding

@app.command()
def run_smtsolver_with_multisetencoding(cfm: CFM):
    path = os.path.join(os.path.abspath(sys.path[0]), "../../z3/z3/build/z3")
    cmd = [path ,'-in','-smt2']
    encoding = create_smt_multiset_encoding(cfm)
    encoding += "(maximize Feature_salami)"
    encoding += "(check-sat)"
    encoding += "(get-model)"
    encoding += "(exit)"
    p = subprocess.run(cmd, stdout=subprocess.PIPE,
                       input=encoding, encoding='ascii')

    print(p.stdout)
    #p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, shell=True)
    #out = p.communicate(input=encoding)
    #result = out.split('\n')
    #for lin in result:
    #    print(lin)


@app.command()
def encode_to_smt_cloning(cfm: CFM) -> str:
    print("Encoding CFM...")
    encoding = ""


    print(encoding)
    return encoding




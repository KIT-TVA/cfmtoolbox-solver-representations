import unittest

from cfmtoolbox.plugins.json_import import import_json
from cfmtoolbox_smt_encoder import run_smt_solver_with_cloning_base_gap_detection, \
    run_smt_solver_with_cloning_base_maximize_cardinalities, \
    run_smt_solver_with_cloning_base_minimize_cardinalities, \
    run_smt_solver_with_cloning_with_child_int_constants_gap_detection, \
    run_smt_solver_with_cloning_with_child_int_constants_maximize_cardinalities, \
    run_smt_solver_with_cloning_with_child_int_constants_minimize_cardinalities


class TestCloningSMT(unittest.TestCase):



   def test_gaps_multiplayer_cloning_basic(self):
       file = open("../cfms/multiplayer.json", "rb")
       self.cfm = import_json(file.read())
       file.close()

       result = run_smt_solver_with_cloning_base_gap_detection(cfm=self.cfm)

       self.assertIn('Gap at: 5 in Feature: Team', result)
       for i in range(9,30):
           self.assertIn('Gap at: ' +  str(i) + ' in Feature: Team', result)

       self.assertIn('Gap at: 30 in Feature: Player', result)


   def test_maximize_cardinalities_multiplayer_cloning_basic(self):
       file = open("../cfms/multiplayer.json", "rb")
       self.cfm = import_json(file.read())
       file.close()

       result = run_smt_solver_with_cloning_base_maximize_cardinalities(cfm=self.cfm)

       self.assertIn('multiplayer_1: 1', result)
       self.assertIn('CentralNode_1: 1', result)
       self.assertIn('Display_1: 1', result)
       self.assertIn('InterTeamCommunication_1: 1', result)
       self.assertIn('Broadcast_1_1: 1', result)
       self.assertIn('Unicast_1_1: 1', result)
       self.assertIn('Team_1: 8', result)
       self.assertIn(' IntraTeamComm_30: 1', result)
       self.assertIn('Broadcast_1_2: 1', result)
       self.assertIn('Wifi_30_1: 1', result)
       self.assertIn('BT_30_1: 1', result)
       self.assertIn('Members_30: 3',result)
       self.assertIn('Player_30_1: 29',result)
       self.assertIn('Leader_30_1: 1',result)
       self.assertIn('ScatteredStrategy_30_1_1: 1',result)
       self.assertIn(' SpecificStrategy_30_1_1: 1',result)

   def test_minimize_cardinalities_multiplayer_cloning_basic(self):
       file = open("../cfms/multiplayer.json", "rb")
       self.cfm = import_json(file.read())
       file.close()

       result = run_smt_solver_with_cloning_base_minimize_cardinalities(cfm=self.cfm)

       self.assertIn('multiplayer_1: 1', result)
       self.assertIn('CentralNode_1: 1', result)
       self.assertIn('Display_1: 1', result)
       self.assertIn('InterTeamCommunication_1: 1', result)
       self.assertIn('Broadcast_1_1: 0', result)
       self.assertIn('Unicast_1_1: 0', result)
       self.assertIn('Team_1: 2', result)
       self.assertIn('IntraTeamComm_30: 0', result)
       self.assertIn('Wifi_30_1: 0', result)
       self.assertIn('BT_30_1: 0', result)
       self.assertIn('Members_30: 0', result)
       self.assertIn('Player_30_1: 0', result)
       self.assertIn('Leader_30_1: 0', result)
       self.assertIn('ScatteredStrategy_30_1_1: 0', result)
       self.assertIn(' SpecificStrategy_30_1_1: 0', result)

   def test_gaps_multiplayer_cloning_with_int_leaves(self):
       file = open("../cfms/multiplayer.json", "rb")
       self.cfm = import_json(file.read())
       file.close()

       result = run_smt_solver_with_cloning_with_child_int_constants_gap_detection(cfm=self.cfm)

       self.assertIn('Gap at: 5 in Feature: Team', result)
       for i in range(9,30):
           self.assertIn('Gap at: ' +  str(i) + ' in Feature: Team', result)

       self.assertIn('Gap at: 30 in Feature: Player', result)


   def test_maximize_cardinalities_multiplayer_cloning_with_int_leaves(self):
       file = open("../cfms/multiplayer.json", "rb")
       self.cfm = import_json(file.read())
       file.close()

       result = run_smt_solver_with_cloning_with_child_int_constants_maximize_cardinalities(cfm=self.cfm)

       self.assertIn('multiplayer_1: 1', result)
       self.assertIn('CentralNode_1: 1', result)
       self.assertIn('Display_1: 1', result)
       self.assertIn('InterTeamCommunication_1: 1', result)
       self.assertIn('Broadcast_1_1: 1', result)
       self.assertIn('Unicast_1_1: 1', result)
       self.assertIn('Team_1: 8', result)
       self.assertIn('IntraTeamComm_30: 0', result)
       self.assertIn('Broadcast_1_2: 1', result)
       self.assertIn('Wifi_30_1: 1', result)
       self.assertIn('BT_30_1: 1', result)
       self.assertIn('Members_30: 1',result)
       self.assertIn('Player_30_1: 29',result)
       self.assertIn('Leader_30_1: 1',result)
       self.assertIn('ScatteredStrategy_30_1_1: 1',result)
       self.assertIn(' SpecificStrategy_30_1_1: 1',result)

   def test_minimize_cardinalities_multiplayer_cloning_with_int_leaves(self):
       file = open("../cfms/multiplayer.json", "rb")
       self.cfm = import_json(file.read())
       file.close()

       result = run_smt_solver_with_cloning_with_child_int_constants_minimize_cardinalities(cfm=self.cfm)

       self.assertIn('multiplayer_1: 1', result)
       self.assertIn('CentralNode_1: 1', result)
       self.assertIn('Display_1: 1', result)
       self.assertIn('InterTeamCommunication_1: 1', result)
       self.assertIn('Broadcast_1_1: 0', result)
       self.assertIn('Unicast_1_1: 0', result)
       self.assertIn('Team_1: 2', result)
       self.assertIn('IntraTeamComm_30: 0', result)
       self.assertIn('Wifi_30_1: 0', result)
       self.assertIn('BT_30_1: 0', result)
       self.assertIn('Members_30: 0', result)
       self.assertIn('Player_30_1: 0', result)
       self.assertIn('Leader_30_1: 0', result)
       self.assertIn('ScatteredStrategy_30_1_1: 0', result)
       self.assertIn(' SpecificStrategy_30_1_1: 0', result)
if __name__ == '__main__':
    unittest.main()

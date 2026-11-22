from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from check_public_safety import BOUNDARY, verify


class PublicSafety(unittest.TestCase):
    def setUp(self):
        self.header = ("ZEXTERN void ZEXPORT foo(void);\n/* ZEXPORT ignored(int); */\n"
                       "ZEXTERN int ZEXPORT bar(char);\n" + BOUNDARY + "\n"
                       "ZEXTERN int ZEXPORTVA gzvprintf(int);")
        self.inventory = {"source_pin": "pin", "apis": [], "sequence_goals": [],
                          "undocumented": {"functions": ["gzvprintf"]}}
        self.registry = {"dispatch": [], "entries": [], "protocols": [],
                         "proved": [], "required": []}
        for name in ("foo", "bar", "gzvprintf"):
            goal = "ZlibF.Spec.Public.Goal." + name + "_safety"
            impl, source = "Zlib.Module." + name, "ZlibF/Zlib/foo.c.lean"
            self.inventory["apis"].append({"function": name, "scope": "lp64-linux", "implementation": impl,
                                           "source": source, "safety_goal": goal})
            self.registry["dispatch"].append((name, impl, source))
            if name != "gzvprintf":
                self.registry["entries"].append((name, goal))
            self.registry["proved"].append((goal, "Proof." + name))
            self.registry["required"].append(goal)
        for name, label in (("inflate", "inflate"), ("deflate", "deflate"),
                            ("inflateBack", "inflate_back"), ("gzip", "gz")):
            sequence = "ZlibF.Spec.Public.Goal." + label + "_sequence"
            self.inventory["sequence_goals"].append(sequence)
            self.registry["protocols"].append((name, sequence + "_safety"))
        extras = [goal for _, goal in self.registry["protocols"]] + ["ZlibF.Spec.Public.Goal.whole_library_safety"]
        for goal in extras:
            self.registry["proved"].append((goal, "Proof.aggregate"))
            self.registry["required"].append(goal)

    def check(self):
        return verify(self.inventory, "pin", self.header, self.registry)

    def test_complete(self):
        self.assertEqual(self.check(), 2)

    def test_pin_and_missing_header_entry(self):
        self.inventory["source_pin"] = "other"
        with self.assertRaisesRegex(ValueError, "source_pin"):
            self.check()
        self.inventory["source_pin"] = "pin"
        self.inventory["apis"].pop(0)
        self.registry["entries"].pop(0)
        with self.assertRaisesRegex(ValueError, "missing.*foo"):
            self.check()

    def test_duplicate_and_misclassified(self):
        self.inventory["apis"].append(self.inventory["apis"][0])
        with self.assertRaisesRegex(ValueError, "duplicate.*foo"):
            self.check()
        self.inventory["apis"].pop()
        self.inventory["undocumented"]["functions"].append("foo")
        with self.assertRaisesRegex(ValueError, "undocumented.*foo"):
            self.check()

    def test_mislinked_contract_or_implementation(self):
        row = self.inventory["apis"][0]
        row["implementation"] = self.inventory["apis"][1]["implementation"]
        with self.assertRaisesRegex(ValueError, "foo.*Call.execute"):
            self.check()
        row["implementation"] = self.registry["dispatch"][0][1]
        row["safety_goal"] = self.inventory["apis"][1]["safety_goal"]
        with self.assertRaisesRegex(ValueError, "foo.*expected"):
            self.check()

    def test_swapped_in_both_sources(self):
        foo, bar = self.inventory["apis"][:2]
        foo["safety_goal"], bar["safety_goal"] = bar["safety_goal"], foo["safety_goal"]
        self.registry["entries"] = [(row["function"], row["safety_goal"]) for row in (foo, bar)]
        with self.assertRaisesRegex(ValueError, "belongs to another function"):
            self.check()

    def test_missing_constructor_or_registry_membership(self):
        entry = self.registry["entries"].pop()
        with self.assertRaisesRegex(ValueError, "PublicEntry.*bar"):
            self.check()
        self.registry["entries"].append(entry)
        self.registry["proved"].pop(0)
        with self.assertRaisesRegex(ValueError, "foo.*proved=False"):
            self.check()

    def test_missing_required_protocol(self):
        self.registry["required"].remove("ZlibF.Spec.Public.Goal.gz_sequence_safety")
        with self.assertRaisesRegex(ValueError, "gz_sequence_safety.*required=False"):
            self.check()

    def test_protocol_swap_or_synchronized_omission(self):
        one, two = self.registry["protocols"][:2]
        self.registry["protocols"][:2] = [(one[0], two[1]), (two[0], one[1])]
        with self.assertRaisesRegex(ValueError, "StreamProtocol selector mismatch"):
            self.check()
        self.registry["protocols"][:2] = [one, two]
        _, goal = self.registry["protocols"].pop()
        self.inventory["sequence_goals"].remove(goal.removesuffix("_safety"))
        with self.assertRaisesRegex(ValueError, "inventory sequence goals.*missing"):
            self.check()

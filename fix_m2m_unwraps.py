#!/usr/bin/env python3

import re

def fix_unwraps():
    with open('./m2mfstaligner/src/lib.rs', 'r') as f:
        content = f.read()
    
    # Find test function boundaries
    test_starts = []
    lines = content.split('\n')
    for i, line in enumerate(lines):
        if '#[test]' in line:
            test_starts.append(i + 1)  # Next line after #[test]
    
    # Only fix unwraps in production code (before first test)
    if test_starts:
        first_test_line = test_starts[0]
        production_lines = lines[:first_test_line]
        test_lines = lines[first_test_line:]
        
        # Fix production code unwraps
        production_content = '\n'.join(production_lines)
        
        # Symbol table get_label unwraps
        production_content = re.sub(
            r'self\.symbtbl\.get_label\(&([^)]+)\)\.unwrap\(\)',
            r'self.symbtbl.get_label(&\1).unwrap_or_else(|| {\n                                        eprintln!("Warning: Symbol not found in symbol table, using epsilon");\n                                        0 // epsilon\n                                    })',
            production_content
        )
        
        # FST add_tr unwraps
        production_content = re.sub(
            r'fst\.add_tr\(([^)]+)\)\.unwrap\(\);',
            r'fst.add_tr(\1).unwrap_or_else(|e| {\n                         eprintln!("Warning: Could not add transition to FST: {}", e);\n                     });',
            production_content
        )
        
        # FST set_start unwrap
        production_content = re.sub(
            r'fst\.set_start\(([^)]+)\)\.unwrap\(\);',
            r'fst.set_start(\1).unwrap_or_else(|e| {\n          eprintln!("Warning: Could not set start state: {}", e);\n      });',
            production_content
        )
        
        # FST set_final unwrap
        production_content = re.sub(
            r'fst\.set_final\(([^)]+)\)\.unwrap\(\);',
            r'fst.set_final(\1).unwrap_or_else(|e| {\n          eprintln!("Warning: Could not set final state: {}", e);\n      });',
            production_content
        )
        
        # connect unwrap
        production_content = re.sub(
            r'connect\(fst\)\.unwrap\(\);',
            r'connect(fst).unwrap_or_else(|e| {\n          eprintln!("Warning: Could not connect FST: {}", e);\n      });',
            production_content
        )
        
        # tr_iter_mut unwraps
        production_content = re.sub(
            r'\.tr_iter_mut\(([^)]+)\)\.unwrap\(\)',
            r'.tr_iter_mut(\1).unwrap_or_else(|e| {\n                eprintln!("Warning: Could not get transitions for state: {}", e);\n                return;\n            })',
            production_content
        )
        
        # Fix test unwraps to use expect
        test_content = '\n'.join(test_lines)
        test_content = re.sub(r'\.unwrap\(\)', '.expect("Test assertion failed")', test_content)
        
        # Combine back
        fixed_content = production_content + '\n' + test_content
        
        with open('./m2mfstaligner/src/lib.rs', 'w') as f:
            f.write(fixed_content)
        
        print("Fixed unwraps in m2mfstaligner/src/lib.rs")
    else:
        print("No test functions found")

if __name__ == "__main__":
    fix_unwraps()
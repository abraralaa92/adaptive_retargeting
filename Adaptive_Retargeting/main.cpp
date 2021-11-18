#include "ScanReg.h"

#define LOG(x) std::cout << x << std::endl;

using namespace std;

string ScanReg::path = "";
unsigned int ScanReg::initial_configuration = 0; //(0) refers to the reset state.
bool ScanReg::optimal_solution = false;
bool ScanReg::retarget_all_TDRs = false;
bool ScanReg::redundant_arbitrary = false; //false for "redundant" and true for "arbitrary".
unsigned int ScanReg::no_CSUs = 0;
measurement solver_return;

//int main(int argc, char** argv) //https://www.tutorialspoint.com/cprogramming/c_command_line_arguments.htmargc 
int main()
{
	//argc: refers to the number of arguments passed, and argv[]: is a pointer array which points to each argument passed to the program
	printf("Please Enter the required parameters with the following order: \n");
	printf("{path, initial_conf, number_of_TFs, Optimal_First, test_all_TDRs, redundant_arbitrary} \n");
	
	double total_execution_time = 0, total_n_conflicts = 0;
	unsigned int no_readings = 1;

	char *inputs[] = { "", "./../../UpperBound_ComputationalModel/UpperBound_Benchmarks/paper_BM/", "0", "3", "1", "0", "1"}; 
	char** argv = inputs;

	//this section is to set class's static variables.
	ScanReg::path = argv[1];
	ScanReg::initial_configuration = stoi(argv[2]);
	ScanReg::no_CSUs = stoi(argv[3]);
	ScanReg::optimal_solution = stoi(argv[4]);
	ScanReg::retarget_all_TDRs = stoi(argv[5]);
	ScanReg::redundant_arbitrary = stoi(argv[6]);

	ScanReg root;
	for (unsigned int reading = 0; reading < no_readings; reading++) //we need to take the average of five readings:
	{
 		
		solver_return = root.call_SAT_retargeter();

		total_execution_time += solver_return.execution_time;
		total_n_conflicts += solver_return.n_conflicts;
	}
	printf("The Average execution time per network = %f s\n", total_execution_time / no_readings);
	printf("The Average No. of Conflicts per network = %f s\n", total_n_conflicts / no_readings);

	root.reset_system();
	root.~ScanReg();

	char x;
	printf("please enter a char to exit");
	scanf("%c", &x);

	return 0;
}
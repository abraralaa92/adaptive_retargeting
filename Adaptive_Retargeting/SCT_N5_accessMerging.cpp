#include "SCT.h"

//static variables (private variables to the scope of this file)
static size_t Expected_no_constraints, Expected_no_SATvariables;
static vector<unsigned int> index_range; //this variable is used to speed up the search in (NW_SAT_variables) vector, where we only search in a specific range of SAT_variables which occur in the specific time frame. Index of this vector represents the timeFrame number; i.e. search_range[1]: means the search range associated with timeFrame(1)
static unsigned int SATvariable_no;
static unsigned int no_timeFrames = 0; //this variable holds the "current", used number of time frames.
static unsigned int delete_threshold = 0; //this variable is used as a threshold between Benchmarks transformation predicates and Read/Write predicates. Hence, it should be updated to the new threshold with each Read/Write predicates of the new incremented time frame. The threshold is used later in (delete_previousTF_Active_ReadWrite_predicates) method to append on the previous SAT problem without its TF's Reagd/Write predicates.
static void (SCT_vertex::*selected_retargeting_model)();

static vector<SCT_vertex> NW_stateElements;		//CSU_Regs(NW_SCBs)
static vector<SCT_vertex> NW_selectElements;	//Shift_Regs(TDRs) 
static vector<_SAT_predicate> NW_SAT_constraints;
static vector<string> NW_SAT_clauses;
static vector<_SAT_variable> NW_SAT_variables; //used to hold the boolean satisfiable values associated to each SAT_variable, which we get from the SAT solver
static vector<vector<_clause>> SAT_output;   //Two dimensional vector where each time frame has its ASP elements. used to hold the retargeting output vectors, by applying the boolean satisfiable values that we have got by the SAT_solver of each node in the network in each TF to get the Active Scan Path.
static vector<NWElement_statistics>NW_TDRs;
static measurement upperBound;

SCT_vertex::SCT_vertex()
{}

SCT_vertex::~SCT_vertex()
{
	//printf("selection_clause Distructed!!\n");
	vector<_clause>().swap(basic_const);
	vector<_clause>().swap(supp_const);
	vector<string>().swap(DSR);
}

void SCT_vertex::reserve_vectors_memory()
{
	//initialize (SATvariable_no) 
	SATvariable_no = 1;
	unsigned int max_no_timeFrames = 20;
	unsigned int multiplier = 10;

	//Following calculations are just based on finding a relation between numbers and figure out how we could put it in a mathematical equation. These expectations are not exact and are not optimum, so this specific prediction section for (Expected_no_nodes, Expected_no_predicates_forSCT, Expected_no_predicates_forSAT, Expected_no_SAT_clauses, Expected_no_SAT_variables) could be optimized in the future.
	Expected_no_constraints = (NW_stateElements.size() * 2) + (NW_stateElements.size() * max_no_timeFrames * multiplier) * (NW_stateElements.size() * 2);	//(part(1): (NW_stateElements.size() * 2): for initial configuration predicates or initial unit clauses [state and initialized (or) initialized and configured variables]. Second part for state transition predicates: (NW_stateElements.size() * max_no_timeFrames * multiplier): assuming that each node/SCT_vertex has an average of a "multiplier" predicates per each time frame. last part for target configurations: (NW_stateElements.size() * 2): 2 for [state and initialized (or) initialized and configured].
	Expected_no_SATvariables = Expected_no_constraints / multiplier;

	NW_SAT_constraints.reserve(Expected_no_constraints);
	NW_SAT_variables.reserve(Expected_no_SATvariables); //number of SAT variables almost equal to the number of predicates

	//this vector is used as an index director to the SAT_variables associated to each timeFrame
	index_range.reserve(max_no_timeFrames + 1); //no_timeFrames; since we need to set the search range for each timeFrame. (+1) to account also initial time frame (t0).
	SAT_output.reserve(max_no_timeFrames + 1);   //(+1) to account also initial time frame (t0). Here we only reserve the outer vector capacity, and in the struct (_clause)'s constructor we reserve the internal vector capacity for each time frame.
}

void SCT_vertex::reset_system()
{
	vector<_SAT_predicate>().swap(NW_SAT_constraints);
	vector<string>().swap(NW_SAT_clauses);
	vector<_SAT_variable>().swap(NW_SAT_variables);
	vector<SCT_vertex>().swap(NW_stateElements);
	vector<SCT_vertex>().swap(NW_selectElements);
	vector<unsigned int>().swap(index_range);
	vector<NWElement_statistics>().swap(NW_TDRs);
	
	//Swapping 2D vectors:
	for (unsigned int i = 0, e = SAT_output.size(); i < e; i++)
		vector<_clause>().swap(SAT_output[i]);
	vector<vector<_clause>>().swap(SAT_output);
}

void SCT_vertex::clear_vectors()
{
	//initialize (SATvariable_no) 
	SATvariable_no = 1;

	NW_SAT_constraints.clear();
	NW_SAT_clauses.clear();
	NW_SAT_variables.clear();
	index_range.clear();
	SAT_output.clear();
	clear_searchSpace();
}

void SCT_vertex::clear_searchSpace()
{
	//The only vector that doesn't change during the lifetime of the retargeting problem is the "selection_clauses/Basic_constraints". The remaining vectors are all correlates with the target configuration and the target_reg. That's why we need to reset it before we load the next target configuration
	for (size_t i = 0, e = NW_stateElements.size(); i < e; i++)
	{
		NW_stateElements[i].relevancy = false; //Reset the flag
		NW_stateElements[i].supp_const.clear();
		NW_stateElements[i].DSR.clear(); //need to be reset with each new target configuration as the DSRs because of supplementary constraints are updated w.r.t the target reg.
	}

	//here we set the target-reg's supplemental constraints
	for (size_t i = 0, e = NW_selectElements.size(); i < e; i++)
		NW_selectElements[i].supp_const.clear();
}

measurement SCT_vertex::call_SAT_retargeter()
{
	setup_the_environment(); //load the basic_const, reserve the required memory and select the retargeting model

	if (!retarget_all_TDRs)
	{
		NW_TDRs.emplace_back(load_target_configuration()); //from the (pdl) file
		NW_TDRs.back().solver_returns.emplace_back(); //adjust a place in the (solver_returns) vector to be "directly" used in setting SAT_solver output values.
		
		if (optimal_solution && no_CSUs == -1)
			setup_the_UB_problem(); //first we need to compute the upper-bound, if it is unkown before we apply the requested retargeting model
		//setup_the_retargeting_problem();
		//print_NWstatistics(true); //means print NW_statistics for this "SPECIFIC" TDR.
	}
	else
	{
		NW_TDRs.reserve(NW_selectElements.size());
		if (optimal_solution && no_CSUs == -1)
			setup_the_UB_problem(); //first we need to compute the upper-bound, if it is unkown before we apply the requested retargeting model
		/*
		for (size_t i = 0, e = NW_selectElements.size(); i < e; i++)
		{
			NW_TDRs.emplace_back(NW_selectElements[i].id);
			NW_TDRs.back().solver_returns.emplace_back(); //adjust a place in the (solver_returns) vector to be "directly" used in setting SAT_solver output values.
			setup_the_retargeting_problem(); //according to the selected target_reg
			clear_vectors(); //reset the system for the next TDR retargeting 
		}
		print_NWstatistics(false); //means print NW_statistics for the whole network for "ALL" Network_TDRS.
		*/
	}

	measurement execution_time(get_avg('E'), get_avg('C'), get_avg('A')); //this is the average of all network's TDRs retargeting times. The average calculated in the main() file, is the average of re-applying the retargeting process on the same network and under the same conditions for number of times (setted by the "no_readings" parameter).
	print_vectors_size_capacity_comparison(); ////Finally I need to 'update' (NW_vectors_sizes) with NW SAT vectors statistics
	reset_system();
	return execution_time;
}

void SCT_vertex::setup_the_environment()
{
	if (!optimal_solution) //means we want the "First_Solution" which depends "only" on (structural and temporal dependency) of the target_reg_SCT
		selected_retargeting_model = &SCT_vertex::first_retargeting_model;

	else //optimal_retargeting
		selected_retargeting_model = &SCT_vertex::optimal_retargeting_model;
	
	set_BasicConstraints(); //here we load the selections for all network scan segments (SCBs and TDRs)
	reserve_vectors_memory();
}

void SCT_vertex::setup_the_retargeting_problem()
{
	if (NW_selectElements[get_selection_clause_index(NW_TDRs.back().reg_id)].basic_const[0].clause == "TRUE")//if this is the case, then it means the target_reg is an "always-active" TDR, and it is already part of the ASP, and hence "no" retargeting problem (either first or optimal retargeting) is exist in the first place to be resolved!!
	{
		no_CSUs = 0;
		NW_TDRs.back().solver_returns.emplace_back(0, 0, 0); //execution_time(a), n_conflicts(b), AccessTime(c)
		generate_output_retargeting_vector();
		compute_no_clockCycles(); //re-compute the Accesstime based on the network ASP.
		print_file(SAT_retargeting_vectors, path + "NW_SCT_to_SAT_retargeting_vectors.txt", "a");
	}
	else
		(*this.*selected_retargeting_model)(); //invoke the selected retargeting model, either it was first/optimal.
}

string SCT_vertex::load_target_configuration()
{
	//set (target_reg) name from "pdl" file
	//"In Future" I need to loop onto "vector<string>NW_TDRs", in order to generate the final report.
	string input_file = path + "NW_smv.pdl";
	std::ifstream data_file(input_file.c_str());
	string line, target_reg = "";
	if (data_file)
	{
		unsigned int itr = 0;

		//it is only one line there.
		getline(data_file, line);
		while (line[itr] != ' ')
			itr++;

		while (line[++itr] != ' ')
			target_reg += line[itr];

		return target_reg;
	}
}

void SCT_vertex::first_retargeting_model()
{
	//Here we call (generate_TReg_SCT) and not (build_search_space): to build the search space with the *min_constraints*; where (TReg_SCT) holds only Structural and Temporal dependencies with the TReg (NO LPC). We are only seeking the retargeting with the first solution which maintain the min number of CSUs.
	set_BasicConstraints();
	set_relevancy(NW_selectElements[get_selection_clause_index(NW_TDRs.back().reg_id)].basic_const); //this holds structural and temporal dependencies. 
	
	if (no_CSUs != -1)
	{
		first_retargeting_oneCall_model();
	}
	else
		first_retargeting_incremental_model();
}

void SCT_vertex::first_retargeting_oneCall_model()
{
	//Here the number of CSUs needed for first_solution is known, and hence we could call/unroll the SAT_Solver for only "one" time, seeking for the retargeting vectors within the min #CSUs.
	no_timeFrames = no_CSUs;

	generate_SAT_instance(); //this would unroll the SAT Solver for only "one" time using the pre-defined number of CSUs.
	convert_constraints_to_CNF();

	if (is_SAT_instance_satisfiable()) //this condition is crucial because the SAT_problem may not have solution at all *using* the assigned number of CSUs
		printf("\nThe Retargeting of (%s) is SATISFIABLE using (%d) CSUs\n", NW_TDRs.back().reg_id.c_str(), no_timeFrames);
}

void SCT_vertex::first_retargeting_incremental_model()
{
	generate_incremental_SAT_instance(); //here we construct an initial SAT_instance for the (TF=0) where it would be used in the "first unrollment" of the SAT_Solver inside the next (while loop).
	convert_constraints_to_CNF();

	while (!is_SAT_instance_satisfiable())
	{
		no_timeFrames++;
		generate_incremental_SAT_instance(); //here we unroll the SAT Solver for a "number" of times until a solution is found. Iinitially (NW_TDRs.back().no_timeFrames = 0).
		convert_constraints_to_CNF();
	}

	no_CSUs = no_timeFrames;
	printf("\nThe Retargeting of (%s) is SATISFIABLE using (%d) CSUs\n", NW_TDRs.back().reg_id.c_str(), no_CSUs);
}

void SCT_vertex::set_BasicConstraints()
{
	string input_file = path + "NW_clauses.txt";
	std::ifstream data_file(input_file.c_str());
	string line;
	if (!data_file)
		printf("Cannot open the File : %s\n", input_file.c_str());

	else
	{
		unsigned int itr = 0;
		string id;
		string selection_clause;
		string len;
		unsigned int length;
		string reset;
		unsigned int reset_value;

		//First line holds NW_stateElements size and second line holds NW_selectElements size.
		getline(data_file, line);
		NW_stateElements.reserve(stoi(line));

		getline(data_file, line);
		NW_selectElements.reserve(stoi(line) + 1); //(+1) in case we need to add ("V.Instrument") through the (UBC) problem.

		while (getline(data_file, line)) //Reads the entire line up to '\n' character or the delimiting character specified. After reading the line, the control goes to the next line in the file. Also, it returns a boolean value of true if the read operation was successful, else false.
		{
			itr = 0;
			id = "";
			selection_clause = "";
			len = "";
			reset = "";

			//{ "In-M1_2/9", "SR-M1_2/8^SR-M1_1/4", 73, 0 }, 
			while (line[itr] != '"')
				itr++; //Do nothing! just increment the counter

			while (line[++itr] != '"')
				id += line[itr];

			while (line[++itr] != '"')
				; //Do nothing! just increment the counter

			while (line[++itr] != '"')
				selection_clause += line[itr];

			while (!isdigit(line[itr]))
				itr++; //Do nothing! just increment the counter

			while (isdigit(line[itr]))
				len += line[itr++];
			length = stoi(len);

			while (!isdigit(line[itr]))
				itr++; //Do nothing! just increment the counter

			while (isdigit(line[itr]))
				reset += line[itr++];
			reset_value = stoi(reset);

			//call initial constructor 
			if (is_SCB(id))
				NW_stateElements.emplace_back(id, length, reset_value, selection_clause); //_clause=NULL because it will be updated after that with a vector of clauses through (split_selection_clause_into_vectorOfClauses) method.initial_configuration represent (initial state and reset state)
			else  //This condition to select all NW_TDRs since they have only select_variables because they are shift_registers, however, other network SCBs are CSU_regs with state and select varaiables which could be updated from one time frame to another with different values until target_reg become part of the ASP.
				NW_selectElements.emplace_back(id, length, reset_value, selection_clause);
		}
	}
}

void SCT_vertex::set_relevancy(vector<_clause>& selections) //this method is setting only "relevancy" flag for all vertices which belongs to search_space
{
	unsigned int index;
	if (selections[0].clause == "TRUE")
		return;
	
	for (size_t i = 0, e = selections.size(); i < e; i++)
	{
		index = get_selection_clause_index(selections[i].clause);
		NW_stateElements[index].relevancy = true;
		set_relevancy(NW_stateElements[index].basic_const); //apply recursion to set the SCB's relevancy because of temporal dependencies also
	}
}

void SCT_vertex::optimal_retargeting_model()
{
	unsigned int index_of_optimal_cost;		//which reflect the min number of Cycles needed for the optimal retargeting.
	double incremental_SAT_solving_time = 0; //the summation of the execution_time of *each* SAT_Solver unrollment time for *each* possible satisfying path, until "all" possible solutions for the retargeting problem are examined.
	NW_TDRs.back().solver_returns.reserve((no_CSUs + 1) * 10);        //(*10): this reservation is only a rnd value we pick without any scientific reason. so we are assuming that each time frame has an average of "10" different possible solutions. We are considering each TF; because when we enter that (#CSUs = 5) to the SAT solver, then it will look for solutions in (TF=0, TF=1, TF=2, TF=3, TF=4, TF=5) that's why we need to take all previous TFs into considerations while reserving the vectors capacity.
	NW_TDRs.back().solver_returns.emplace_back(); //adjust a place in the (solver_returns) vector to be "directly" used in setting SAT_solver output values.
	
	build_the_retargeting_searchSpace(NW_selectElements[get_selection_clause_index(NW_TDRs.back().reg_id)]);

	while (no_timeFrames <= no_CSUs)
	{
		generate_incremental_SAT_instance(); //here we input the (UB_CSUs + SCT[SD+TD+LPC]).
		convert_constraints_to_CNF();

		//In optimal retargeting we apply multiple calls to the SAT_solver using (is_SAT_instance_satisfiable()) to search for all possible solutions in the search space using the assigned no_timeFrames until the whole space is examined and traversed and no other solutions could possibly exist.
		while (is_SAT_instance_satisfiable()) //This condition means it is not (UNSATISFIABLE) and the SAT_solver still finding other possible solutions.
			update_SAT_instance(path + "NW_SCT_to_SAT.txt");	//update SAT_problem: append the "NEGATION" of the found solution to the SAT_problem to look for other solutions, until the solver returns (UNSATISFIABLE) or (empty) satisfiable_string inidicating that there is no other "different" solutions with this upper_bound number of CSUs.

		no_timeFrames++;
	}

	index_of_optimal_cost = 0; // like min = x[0]; here we only set min value to the first index in the vector and compare others to it.
	for (size_t i = 0, e = NW_TDRs.back().solver_returns.size(); i < e; i++)
	{
		incremental_SAT_solving_time += NW_TDRs.back().solver_returns[i].execution_time; //this holds the execution time of each posiible retargeting solution.
		if (NW_TDRs.back().solver_returns[i].AccessTime < NW_TDRs.back().solver_returns[index_of_optimal_cost].AccessTime)
			index_of_optimal_cost = i;
	}
	printf("\n***Min number of clock cycles for the retargeting of (%s), using (%d) CSUs = %d***\n", NW_TDRs.back().reg_id.c_str(), NW_TDRs.back().solver_returns[index_of_optimal_cost].no_CSUs, NW_TDRs.back().solver_returns[index_of_optimal_cost].AccessTime);
	printf("Retargeting problem took (%f) sec\n", incremental_SAT_solving_time);
}

void SCT_vertex::update_SAT_instance(const string& file_name)
{
	//This method is used to append only the "negation" of the satisfiable_string to the SAT_problem but we need to (reWrite) the "NW_SCT_to_SAT.txt" file because the number of SAT clauses has been updated and we need to reflect that in the first line of the CNF file be reWriting it, where there is no any other possibility to do this except bt the reWriting. https://stackoverflow.com/questions/9505085/replace-a-line-in-text-file
	//First update the number of SAT clauses to include the (negated_staisfiable_str) clause also, using the updated size value (NW_SAT_clauses.size()).
	NW_SAT_clauses[0] = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_clauses.size());

	//Second append the (negated_staisfiable_str) to the original SAT problem.
	NW_SAT_clauses.emplace_back(get_negated_string(NW_TDRs.back().solver_returns.back().satisfiable_string));

	//Third reWrite the SAT problem taking into consideration all found solution to let the SAT solver seek for other different solutions.
	print_file(SAT_clauses, path + "NW_SCT_to_SAT.txt", "w");

	//Finally reset the (SAT_output) to be used in the next retargeting.
	SAT_output.clear();
}

void SCT_vertex::build_the_UB_searchSpace(SCT_vertex& target_configuration) //the search space changes constantly with each new target configuration. This we we use the () parameter as an input for this function, 
{
	//initially we have loaded the target configurations and the set of basic dependencies
	set_relevancy(target_configuration.basic_const); //set relevancy with respect to basic constraints, inside the (add_SupplementaryConstraints) method: we set relevancy based on supplemental constraints.
	set_DSRs_becOF_basicConstraints();
	set_SupplementaryConstraints(target_configuration); //append (SC) after adding the (BC) with the target configuration.
	update_DSRs_becOF_supplementalConstraints(); //The order here is very important, as we have to call this method after we set the supplementary constraints of relevant SCBs. this is needed while computing the max number of CSUs as it is used through the (has_any_dependenceRelation_with_any_relevantSCB) method; to check when: 1) if the selected controller is dependent by any network SCB or not. 2)in model_3 to check when the Configured flag could be fired; since the network has no specific (target_state) to follow.
}

void SCT_vertex::build_the_retargeting_searchSpace(SCT_vertex& target_register) //the search space changes constantly with each new target configuration. This we we use the () parameter as an input for this function, 
{
	// For the retargeting problem we need to append all the SCB that relates to the retargeting problem either due to a primary or a supplementary dependency.
	set_relevancy(target_register.basic_const);		//First, we set all "relevant" SCBs to the retargeting problem
	set_SupplementaryConstraints(target_register);					//Next, we set the Supplemental Constraints for the "relevant" SCBs and the "target_reg"
}

void SCT_vertex::setup_the_UB_problem()
{
	//for all models we refer to the UB_Model from "any initial configuration".
	if (UB_Model == 1)
		UpperBound_model_for_SpecificRetargeting();
	else if (UB_Model == 2)
		UpperBound_model_for_anyElementaryRetargeting();
	else if (UB_Model == 3)
		UpperBound_model_for_anyNWConfiguration();
	else if (UB_Model == 4)
		UpperBound_model_for_anyNWRetargeting();
}

void SCT_vertex::UpperBound_model_for_SpecificRetargeting()
{
	double model_construction_time = 0;
	unsigned targetReg_index = get_selection_clause_index(NW_TDRs.back().reg_id);
	
	auto start = std::chrono::steady_clock::now();
		build_the_UB_searchSpace(NW_selectElements[targetReg_index]); //Calling of this method would embed through the SCT: [SCBs with structural dependency + SCBs with temporal dependency + SCBs with longest path constraint]. we have to consider the longest retargeting path because it might achieve the optimal retargeting cost.
	auto elapsed = std::chrono::steady_clock::now() - start;
	model_construction_time += std::chrono::duration<double>(elapsed).count();

	//Apply incremental SAT until a solution is found for this satisfying problem; by finding it we have the max, effective (with no pessimism inshaa Allah) number of CSUs to find the optimal retargeting vectors.
	while (upperBound.satisfiable_string.length() == 0) //means the problem is "UNSATISFIABLE"
	{
		generate_incremental_SAT_instance_for_anyInitialConfiguration(NW_selectElements[targetReg_index].basic_const, NW_selectElements[targetReg_index].supp_const);
		convert_constraints_to_CNF();
		run_SAT_solver_withNoPrint(path + "NW_SCT_to_SAT.txt", upperBound);
		//convert_constraints_to_CNF_withIDs(); //this method is only used for Eye's check
		if (upperBound.satisfiable_string.length() == 0)
			no_timeFrames++;
		else
		{
			no_CSUs = no_timeFrames;
			printf("Max number of CSUs for (%s) = (%d) CSUs\n", NW_TDRs.back().reg_id.c_str(), no_CSUs);
			printf("Building the search space of the upper-bound problem took (%f) sec\n", model_construction_time);
			printf("Solving the upper-bound problem took (%f) sec\n", upperBound.execution_time);
		}
	}

	//Finally, we prepare the environment for the (retargeting) problem, after resolving the UBC problem.
	no_timeFrames = 0;
	clear_vectors();
}

void SCT_vertex::UpperBound_model_for_anyElementaryRetargeting()
{
	//for this type, we want to determine the max no_CSUs to go from (any_initial_config) to (any_target_config) with No Pessimism inshaa Allah.
	double model_construction_time = 0;
	double UB_generation_time = 0; //the summation of the execution_time of *each* SAT_Solver unrollment time for *each* TDR_UB satisfying, until the UB statisfying of all NW_TDRs is computed and determined.
	unsigned int max_no_CSUs = 0, sum = 0;
	
	for (unsigned int i = 0, e = NW_selectElements.size(); i < e; i++)
	{
		if (NW_selectElements[i].basic_const[0].clause != "TRUE")//if this is the case, then it means the TDR is an always-active TDR, and it is already part of the ASP, and since the (max_no_CSUs) initiated to (0), then Nothing need to be added!!
		{
			//next step: is to build the search space associated with the assigned target_reg, for the purpose of the upper-bound computations. UB_SCT: (Structural dependency + Temporal dependedency + LPC dependency)
			auto start = std::chrono::steady_clock::now();
				build_the_UB_searchSpace(NW_selectElements[i]);
			auto elapsed = std::chrono::steady_clock::now() - start;
			model_construction_time += std::chrono::duration<double>(elapsed).count();

			//Apply incremental SAT until a solution is found for this satisfying problem; by finding it we have the max, effective (with no pessimism inshaa Allah) number of CSUs to find the optimal retargeting vectors.
			while (upperBound.satisfiable_string.length() == 0) //means the problem is "UNSATISFIABLE"
			{
				generate_incremental_SAT_instance_for_anyInitialConfiguration(NW_selectElements[i].basic_const, NW_selectElements[i].supp_const);
				convert_constraints_to_CNF();
				run_SAT_solver_withNoPrint(path + "NW_SCT_to_SAT.txt", upperBound);
				//convert_constraints_to_CNF_withIDs(); //this method is only used for Eye's check
				if (upperBound.satisfiable_string.length() == 0)
					no_timeFrames++;
				else
				{
					sum += no_timeFrames;
					UB_generation_time += upperBound.execution_time;
					if (max_no_CSUs < no_timeFrames)
						max_no_CSUs = no_timeFrames; //update with the max no of CSUs.
				}
			}

			//Reset the environment for the "next" TDR_UB computations.
			no_timeFrames = 0;
			upperBound.clear();
			clear_vectors(); //we need to clear all used variables in the system including the SCT; since I have to create a new one associated with every "NW_TDR" Upper-Bound.
		}
	}

	no_CSUs = max_no_CSUs;
	printf("Average number of CSUs for any TDR Retargeting, starting from (any Initial Configuration) to the (Target Configuration) = (%f) CSUs\n", ((float)sum / NW_selectElements.size()));
	printf("Max number of CSUs = (%d) CSUs\n", no_CSUs);
	printf("Building the search space of the upper-bound problem took (%f) sec\n", model_construction_time);
	printf("Solving the upper-bound problem took (%f) sec\n", UB_generation_time);
}

void SCT_vertex::UpperBound_model_for_anyNWConfiguration()
{
	//for this type, we want to determine the max no_CSUs to go from (any_initial_config) to (any_target_config).
	double model_construction_time = 0;
	SCT_vertex target_configuration; //here we need to append the clauses of *all* NW SCBs with "any" randomly selected state, as our concen is to set all network SCBs flags to TRUE, irrespective to the associated state. Meaning the network can be updated with any target state.
	target_configuration.basic_const.reserve(NW_stateElements.size());
	for (unsigned int i = 0, e = NW_stateElements.size(); i < e; i++)
		target_configuration.basic_const.emplace_back(NW_stateElements[i].id, -1); //(-1): we push "any" target state
		
	auto start = std::chrono::steady_clock::now();
		build_the_UB_searchSpace(target_configuration);
	auto elapsed = std::chrono::steady_clock::now() - start;
	model_construction_time += std::chrono::duration<double>(elapsed).count();

	//Apply incremental SAT until a solution is found for this satisfying problem; by finding it we have the max, effective (with no pessimism inshaa Allah) number of CSUs to find the optimal retargeting vectors.
	while (upperBound.satisfiable_string.length() == 0) //means the problem is "UNSATISFIABLE"
	{
		generate_incremental_SAT_instance_for_anyInitialConfiguration(target_configuration.basic_const, target_configuration.supp_const); //(target_configuration.supp_const) would be "vector<_clause>()" or an empty vector, as no supplemental constraints are appended to this model, only model (1) and model (2) may have.
		convert_constraints_to_CNF();
		run_SAT_solver_withNoPrint(path + "NW_SCT_to_SAT.txt", upperBound);
		//convert_constraints_to_CNF_withIDs(); //this method is only used for Eye's check
		if (upperBound.satisfiable_string.length() == 0)
			no_timeFrames++;
		else
		{
			no_CSUs = no_timeFrames;
			printf("Max number of CSUs for the whole NW, starting from (any Initial Configuration) to (any Target Configuration) = (%d) CSUs\n", no_CSUs);
			printf("Building the search space of the upper-bound problem took (%f) sec\n", model_construction_time);
			printf("Solving the upper-bound problem took (%f) sec\n", upperBound.execution_time);
		}
	}

	//Finally, we prepare the environment for the (retargeting) problem, after resolving the UBC problem.
	no_timeFrames = 0;
	clear_vectors();
}

void SCT_vertex::UpperBound_model_for_anyNWRetargeting()
{
	//for this type, we want to determine the max no_CSUs to go from (any_initial_config) to (any_target_config) with No Pessimism inshaa Allah.
	double model_construction_time = 0;
	double UB_generation_time = 0; //the summation of the execution_time of *each* SAT_Solver unrollment time for *each* TDR_UB satisfying, until the UB statisfying of all NW_TDRs is computed and determined.
	unsigned int max_no_CSUs = 0;
	vector<string> Traversed_TDRs;  //This vector is used as a marker for all previously accessed TDRs.
	vector <SCT_vertex> accessMerged_configuration;
	Traversed_TDRs.reserve(NW_selectElements.size()); //Where maximum all NW_TDRs are merged in one longest access merged path!!
	accessMerged_configuration.reserve(50);
	accessMerged_configuration.emplace_back();
	accessMerged_configuration.back().basic_const.reserve(30);

	for (unsigned int i = 0; i < 3; i++)
	{
		for (unsigned int j = 3; j < 6; j++)
		{
			for (unsigned int k = 6; k < 9; k++)
			{
				accessMerged_configuration.back().id = NW_selectElements[i].id + "_" + NW_selectElements[j].id + "_" + NW_selectElements[k].id;
				for (unsigned int index = 0, e = NW_selectElements[i].basic_const.size(); index < e; index++)
					accessMerged_configuration.back().basic_const.emplace_back(NW_selectElements[i].basic_const[index]);
				for (unsigned int index = 0, e = NW_selectElements[j].basic_const.size(); index < e; index++)
					accessMerged_configuration.back().basic_const.emplace_back(NW_selectElements[j].basic_const[index]);
				for (unsigned int index = 0, e = NW_selectElements[k].basic_const.size(); index < e; index++)
					accessMerged_configuration.back().basic_const.emplace_back(NW_selectElements[k].basic_const[index]);

				accessMerged_configuration.emplace_back();
				accessMerged_configuration.back().basic_const.reserve(30);
			}
		}
	}
	for (unsigned int TDR_index = 0, e = accessMerged_configuration.size() - 1; TDR_index < e; TDR_index++)
	{
		auto start = std::chrono::steady_clock::now();
		build_the_UB_searchSpace(accessMerged_configuration[TDR_index]);
		auto elapsed = std::chrono::steady_clock::now() - start;
		model_construction_time += std::chrono::duration<double>(elapsed).count();

		//Apply incremental SAT until a solution is found for this satisfying problem; by finding it we have the max, effective (with no pessimism inshaa Allah) number of CSUs to find the optimal retargeting vectors.
		while (upperBound.satisfiable_string.length() == 0) //means the problem is "UNSATISFIABLE"
		{
			generate_incremental_SAT_instance_for_anyInitialConfiguration(accessMerged_configuration[TDR_index].basic_const, accessMerged_configuration[TDR_index].supp_const); //(target_configuration.supp_const) would be "vector<_clause>()" or an empty vector, as no supplemental constraints are appended to this model, only model (1) and model (2) may have.
			convert_constraints_to_CNF();
			run_SAT_solver_withNoPrint(path + "NW_SCT_to_SAT.txt", upperBound);
			convert_constraints_to_CNF_withIDs(); //this method is only used for Eye's check
			if (upperBound.satisfiable_string.length() == 0)
				no_timeFrames++;
			else
			{
				UB_generation_time += upperBound.execution_time;
				if (max_no_CSUs < no_timeFrames)
					max_no_CSUs = no_timeFrames; //update with the max no of CSUs.
			}
		}

		//Reset the environment for the "next" Access_merged computational path.
		no_timeFrames = 0;
		upperBound.clear(); //clear the records associated with the finished scanning TDR
		clear_vectors(); //we need to clear all used variables in the system including the SCT; since I have to create a new one associated with every network configuration.
	}
	/*accessMerged_configuration.reserve(NW_selectElements.size());

	for (unsigned int TDR_index = 0, e = NW_selectElements.size(); TDR_index < e; TDR_index++) //e = NW_selectElements.size() - 1: (-1) to exclude the "V.Instrument" from the for loop.
	{
		if (find(Traversed_TDRs.begin(), Traversed_TDRs.end(), NW_selectElements[TDR_index].id) == Traversed_TDRs.end()) //We only consider the "NOT-Traversed" before TDRs as an *opening* for the construction of Access Merged paths. If the TDR was not traversed anytime before, then we need to consider its longest access merged path
		{
			if (NW_selectElements[TDR_index].basic_const[0].clause != "TRUE") //where always-active TDRs have no impact on increasing the network's upper bound.
			{
				set_longest_AccessMerged_configuration(TDR_index, Traversed_TDRs, accessMerged_configuration.basic_const);

				//next step: is to build the SCT associated with the Access Merged target configuration
				auto start = std::chrono::steady_clock::now();
					build_the_UB_searchSpace(accessMerged_configuration);
				auto elapsed = std::chrono::steady_clock::now() - start;
				model_construction_time += std::chrono::duration<double>(elapsed).count();

				//Apply incremental SAT until a solution is found for this satisfying problem; by finding it we have the max, effective (with no pessimism inshaa Allah) number of CSUs to find the optimal retargeting vectors.
				while (upperBound.satisfiable_string.length() == 0) //means the problem is "UNSATISFIABLE"
				{
					generate_incremental_SAT_instance_for_anyInitialConfiguration(accessMerged_configuration.basic_const, accessMerged_configuration.supp_const); //(target_configuration.supp_const) would be "vector<_clause>()" or an empty vector, as no supplemental constraints are appended to this model, only model (1) and model (2) may have.
					convert_constraints_to_CNF();
					run_SAT_solver_withNoPrint(path + "NW_SCT_to_SAT.txt", upperBound);
					convert_constraints_to_CNF_withIDs(); //this method is only used for Eye's check
					if (upperBound.satisfiable_string.length() == 0)
						no_timeFrames++;
					else
					{
						UB_generation_time += upperBound.execution_time;
						if (max_no_CSUs < no_timeFrames)
							max_no_CSUs = no_timeFrames; //update with the max no of CSUs.
					}
				}

				//Reset the environment for the "next" Access_merged computational path.
				no_timeFrames = 0;
				upperBound.clear(); //clear the records associated with the finished scanning TDR
				accessMerged_configuration.basic_const.clear();//Reset the Access_Merged configuration before any "new" use
				clear_vectors(); //we need to clear all used variables in the system including the SCT; since I have to create a new one associated with every network configuration.
			}
		}
	}
	*/


	no_CSUs = max_no_CSUs;
	printf("Max number of CSUs for the whole NW, starting from (any Initial Configuration) to (any Target Configuration) and with (NO Pessimism) = (%d) CSUs\n", no_CSUs);
	printf("Building the search space of the upper-bound problem took (%f) sec\n", model_construction_time);
	printf("Solving the upper-bound problem took (%f) sec\n", UB_generation_time);

	//Finally, we prepare the environment for the (retargeting) problem, after resolving the UBC problem.
	vector<string>().swap(Traversed_TDRs);
	//this->~accessMerged_configuration();
}

void SCT_vertex::generate_SAT_instance()
{
	initial_configuration_constraints();

	for (unsigned int t = 0; t < no_CSUs; t++)  //notice that we used here (no_CSUs) and not (no_timeFrames) as usual, as we use (no_timeFrames) if we are applying the incremental SAT model, until the (no_CSUs) reaches the (no_timeFrames). 
	{
		//Here we set the SAT_variables' search range for time frame "(t+1)"
		index_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with timeFrame/index (t+1) not (t).
		StateTransition_monitoring_constraints(t, t + 1);
	}

	target_configuration_constraints();
	NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size();//set the number of (SAT_variables) to the "first_chosen" target_reg.
}

void SCT_vertex::generate_incremental_SAT_instance()
{
	if (no_timeFrames == 0) //if this is the "initial" time frame:
	{
		initial_configuration_constraints();
		target_configuration_constraints();

		NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size();//set the number of (SAT_variables), "initially".
	}
	else //here we use the (incremental_SAT) in successor time frames. 
	{
		//First we remove the predicates associated with the previous time frame
		delete_previousTF_target_configuration_constraints();

		//add the predicates associated with the "just added" time frame.
		index_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with timeFrame/index (t+1) not (t).
		StateTransition_monitoring_constraints(no_timeFrames - 1, no_timeFrames);

		target_configuration_constraints(); //regenerate it for using the "incremental" number of time frames.
		NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size(); //"update" the number of (SAT_variables) to the "new" target_reg.
	}
}

void SCT_vertex::generate_incremental_SAT_instance_for_anyInitialConfiguration(vector<_clause>& targetConfig_BC, vector<_clause>& targetConfig_SC)
{
	//this method is called when (no_CSUs == -1) for the purpose of "Upper-Bound Computation" SAT problems, since in "retargeting" problems we must start from some known/defined/initialized network_state.
	if (no_timeFrames == 0) //if this is the "initial" time frame:
	{
		any_initial_configuration_constraints();
		if (UB_Model == 3) //means the calling for this method (derive_incremental_SAT_predicates) was linked by an (UBC) problem for (NW_UB), seeking for the max number of CSUs capable to apply any NW_TDR retargeting starting from any_initial configuration. 
			any_target_configuration_constraints_for_initialTF(); //false means "First" time frame. (Configured)flags are used to formulate a SAT problem which should be(useful, applicable) for "any target configuration". initially in timeFrame=0, they all should be set to false

		target_configuration_constraints_for_anyInitialConfiguration(targetConfig_BC, targetConfig_SC);
		NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size();//set the number of (SAT_variables), "initially".
	}
	else //here we use the (incremental_SAT) in successor time frames. 
	{
		//First we remove the predicates associated with the previous time frame
		delete_previousTF_target_configuration_constraints();

		//add the predicates associated with the "just added" time frame.
		index_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with the "new incremented" timeFrame.
		InitializedSignal_monitoring_constraints(no_timeFrames - 1, no_timeFrames);	//then I should include initial flags predicates for the initially (unkown/uninitialized) SCB.state.
		StateTransition_monitoring_constraints_for_anyInitialConfiguration(no_timeFrames - 1, no_timeFrames);

		if (UB_Model == 3)			//in case of "any target configuration" model, we append the updating predicates for the "Configure" flags for each SCB in the network and keep these flags "stably" updated.
			ConfiguredSignal_monitoring_constraints_for_anyInitialConfiguration(no_timeFrames - 1, no_timeFrames);

		target_configuration_constraints_for_anyInitialConfiguration(targetConfig_BC, targetConfig_SC); //regenerate it, using the "incremented" number of time frames.
		NW_TDRs.back().n_SAT_variables = NW_SAT_variables.size(); //"update" the number of (SAT_variables) to the "new" target_reg.
	}
}

void SCT_vertex::delete_previousTF_target_configuration_constraints()
{
	for (unsigned int i = NW_SAT_constraints.size(), s = delete_threshold; i > s; i--)
		NW_SAT_constraints.erase(NW_SAT_constraints.end() - 1);
}

void SCT_vertex::initial_configuration_constraints()
{
	index_range.emplace_back(NW_SAT_variables.size());  //this is the NW_SAT_variables's search_range for time frame(t0). it means the search_range of SAT_variables associated with timeFrame(0) starts from index[0], where initially: (NW_SAT_variables.size()=0).

	for (size_t i = 0, e = NW_stateElements.size(); i < e; i++)
	{
		if (NW_stateElements[i].relevancy) // other/excluded SCBs will be keeped at (zero) state each time frame; they would not be included in the SAT problem neither in the proplem's search space.
		{
			//this is for (state) variable: type(1), we only add the SCB.state to NW_SAT_variables, without NW_SAT_predicates.
			NW_SAT_variables.emplace_back(NW_stateElements[i].id, 0, 1, SATvariable_no++);
			NW_SAT_constraints.emplace_back(NW_stateElements[i].id, 0, 1, initial_configuration); //in retargeting we need to go from "certain" initial configuration, to a "certain" target configuration. It can't be vague,unkwon or uninitialized like in (UBC) SAT problems. 
		}
	}
}

void SCT_vertex::any_initial_configuration_constraints()
{
	//this type of predicates is only used with (upper bound computations) where we set the max no_CSUs for a network with "any_initial_configurations".
	index_range.emplace_back(NW_SAT_variables.size());  //this is the NW_SAT_variables's search_range for time frame(t0). it means the search_range of SAT_variables associated with timeFrame(0) starts from index[0], where initially: (NW_SAT_variables.size()=0).

	for (size_t i = 0, e = NW_stateElements.size(); i < e; i++)
	{
		if (NW_stateElements[i].relevancy) // other "irrelevant" SCBs will be keeped at (reset) state each time frame; as they would not be included in the SAT problem neither in the proplem's search space.
		{
			//this is for (initialized) flag: type(2)
			NW_SAT_constraints.emplace_back(NW_stateElements[i].id, 0, 2, 0); //(0): all flags are initially,(t0), (false)
			NW_SAT_variables.emplace_back(NW_stateElements[i].id, 0, 2, SATvariable_no++);

			//this is for (state) variable: type(1), we only add the SCB.state to NW_SAT_variables, without NW_SAT_predicates; Since we want the SAT problem depends only the initialized flags' value irrespective of the network initial configurations.
			NW_SAT_variables.emplace_back(NW_stateElements[i].id, 0, 1, SATvariable_no++);
		}
	}
}

void SCT_vertex::any_target_configuration_constraints_for_initialTF()
{
	for (size_t i = 0, e = NW_stateElements.size(); i < e; i++)
	{
		//if (NW_stateElements[i].relevancy) //No need to check; since Configured flags are appended for all NW_SCBs.
		{
			//this is for (Configured) flag: type(3) 
			NW_SAT_constraints.emplace_back(NW_stateElements[i].id, no_timeFrames, 3, 0); 
			NW_SAT_variables.emplace_back(NW_stateElements[i].id, no_timeFrames, 3, SATvariable_no++);
		}
	}
}

void SCT_vertex::any_target_configuration_constraints_for_lastTF()
{
	for (size_t i = 0, e = NW_stateElements.size(); i < e; i++)
		NW_SAT_constraints.emplace_back(NW_stateElements[i].id, no_timeFrames, 3, 1);
		//NW_SAT_variables.emplace_back(NW_stateElements[i].id, no_timeFrames, 3, SATvariable_no++);  //We apply "No" incremental for the SAT variables as there were already considered in the state_transition predicates from (tk-1)->(tk)
}

void SCT_vertex::StateTransition_monitoring_constraints(unsigned int fromTF, unsigned int toTF)
{
	//Notes: this is the only method which should set the "state" variable, because the RHS in the implication relation generated from the SCT, holds the "state" values (or the address inputs of the muxes) which we need to *satisfy*
	//includes both state elements transition and active tranition in a combined implication realtion.
	//in this method I could update only the states of (SIBs, SCBs) if it is Active. However, for state Elements (other than the target reg) its states should be the same (Equilvalent relation)
	//for SIB NWs: we set (Non interesred variables) to reset state, while all other SCT's variables are activated based on the selection clauses states. However, for MUX NWs: (all variables) are activated based on the selection clauses states, this could be handeled by checking first the value of (belongsTo_SCT) attribute, where it is always equal to true for MUX NWs.
	
	for (size_t i = 0, e1 = NW_stateElements.size(); i < e1; i++)
	{
		if (NW_stateElements[i].relevancy == true)
		{
			NW_SAT_variables.emplace_back(NW_stateElements[i].id, toTF, 1, SATvariable_no++);

			if (NW_stateElements[i].basic_const[0].clause != "TRUE")
			{
				//Each literal from the "RHS" should be inserted in a seperate predicate; because SAT literals in the "RHS" are (ANDed) together so, we can seperate them into multiple (ANDed predicates).
				//RHS literals are XORed, so for each (NW_clauses[i].clause[j]) we have to insert two predicate. [A XOR B --> C] is the same as [!A OR B OR C, A OR !B OR C]

				for (size_t j = 0, e2 = NW_stateElements[i].basic_const.size(); j < e2; j++)
				{
					NW_SAT_constraints.emplace_back(3); // needs (3) for: LHS(fromTF) XOR LHS(toTF)--> RHS(fromTF)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 0);	//state=0 since we implement (!A OR B OR C)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 1, NW_stateElements[i].basic_const[j].state);

					NW_SAT_constraints.emplace_back(3);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 1);	//state=1 since we implement (A OR !B OR C)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 1, NW_stateElements[i].basic_const[j].state);
				}
			}
			else
			{
				//state = (1) and (0) to insert (state(SR1, t1) OR !state(SR1, t1)) indicating this is an "Active" node
				NW_SAT_constraints.emplace_back(2);

				//here both are inserted in the same statement because they are (ORed) not (ANDed): {state(SR1, t1) OR !state(SR1, t1)}, so it is only *one* statement with *two* literals
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
			}
		}
	}
}

void SCT_vertex::StateTransition_monitoring_constraints_for_anyInitialConfiguration(unsigned int fromTF, unsigned int toTF)
{
	for (size_t i = 0, e1 = NW_stateElements.size(); i < e1; i++)
	{
		if (NW_stateElements[i].relevancy == true)
		{
			NW_SAT_variables.emplace_back(NW_stateElements[i].id, toTF, 1, SATvariable_no++);

			if (NW_stateElements[i].basic_const[0].clause != "TRUE")
			{
				//First loop for: Basic_Constraints
				for (size_t j = 0, e2 = NW_stateElements[i].basic_const.size(); j < e2; j++)
				{
					//This is for the "initialized_flag" variables dependency: to make sure that the SCB "state" value, was first initialized through setting the "initialized_flag".
					NW_SAT_constraints.emplace_back(3); // needs (3) for: LHS(fromTF) XOR LHS(toTF)--> RHS.initialized_flag(fromTF)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 0);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 2, 1);

					NW_SAT_constraints.emplace_back(3);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 2, 1);

					//This is for the "state" variables dependency: to make sure that the configured SCB is now part of the ASP. 
					NW_SAT_constraints.emplace_back(3); // needs (3) for: LHS(fromTF) XOR LHS(toTF)--> RHS(fromTF)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 0);     //state=0 since we implement (!A OR B OR C)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 1, NW_stateElements[i].basic_const[j].state);

					NW_SAT_constraints.emplace_back(3);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 1);	 //state=1 since we implement (A OR !B OR C)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 1, NW_stateElements[i].basic_const[j].state);
				}
				//Second loop for: Supplementary_Constraints
				for (size_t j = 0, e2 = NW_stateElements[i].supp_const.size(); j < e2; j++)
				{
					//This is for the "initialized_flag" variables dependency: to make sure that the SCB "state" value, was first initialized through setting the "initialized_flag".
					NW_SAT_constraints.emplace_back(3); // needs (3) for: LHS(fromTF) XOR LHS(toTF)--> RHS.initialized_flag(fromTF)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 0);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 2, 1);

					NW_SAT_constraints.emplace_back(3);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 2, 1);
					
					//This is for the "state" variables dependency: to make sure that the configured SCB is now part of the ASP. 
					NW_SAT_constraints.emplace_back(3); // needs (3) for: LHS(fromTF) XOR LHS(toTF)--> RHS(fromTF)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 0);     //state=0 since we implement (!A OR B OR C)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 1, NW_stateElements[i].supp_const[j].state);

					NW_SAT_constraints.emplace_back(3);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 1, 1);	 //state=1 since we implement (A OR !B OR C)
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 1, NW_stateElements[i].supp_const[j].state);
				}
			}
			else //here for always_active SCBs, we don't check on flags; because if they are now part of the ASP, then they should be initialized with any shifted bits.
			{
				//state = (1) and (0) to insert (state(SR1, t1) OR !state(SR1, t1)) indicating this is an "Active" node
				NW_SAT_constraints.emplace_back(2);

				//here both are inserted in the same statement because they are (ORed) not (ANDed): {state(SR1, t1) OR !state(SR1, t1)}, so it is only *one* statement with *two* literals
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
			}
		}
	}
}

void SCT_vertex::InitializedSignal_monitoring_constraints(unsigned int fromTF, unsigned int toTF)
{
	for (size_t i = 0, e1 = NW_stateElements.size(); i < e1; i++)
	{
		if (NW_stateElements[i].relevancy)
		{
			//this is for the (initialized) flag: type(2)
			NW_SAT_variables.emplace_back(NW_stateElements[i].id, toTF, 2, SATvariable_no++);

			if (NW_stateElements[i].basic_const[0].clause != "TRUE")
			{
				//these predicates are constructed to "set" the stateElement's initialized flag based on the validation of "all" actiavtion conditions or not.
				//(!cond_A(fromTF) || !cond_A_initialized(fromTF) || !cond_B(fromTF) || !cond_B_initialized(fromTF) || .. || SCB.initialized(toTF))
				NW_SAT_constraints.emplace_back((NW_stateElements[i].basic_const.size() * 2) + (NW_stateElements[i].supp_const.size() * 2) + 1);	//(*2): one for the (state) variable and another one for the (initialized_flag) variable associated with previous time frame or (fromTF). Another incremental is added foe supplementary constraints. (+1): for the initialized_flag(toTF) literal.
				//First loop for: Basic Constraints
				for (size_t j = 0, e2 = NW_stateElements[i].basic_const.size(); j < e2; j++)
				{
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 2, 0); //(0) means !initialized_flag.
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 1, !NW_stateElements[i].basic_const[j].state);
				}
				//Second loop for: Supplementary Constraints
				for (size_t j = 0, e2 = NW_stateElements[i].supp_const.size(); j < e2; j++)
				{
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 2, 0); //(0) means !initialized_flag.
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 1, !NW_stateElements[i].supp_const[j].state);
				}
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 1);

				//these predicates are constructed to "set" the stateElement's flag based on previous time frame flag's state. if the previous condition is not for this time, however, the initialized_flag for this SCB was already set through any previous time frame, then the flag should keeps its previos state stably at the "same_fired_state".  
				//(!SCB.initialized(fromTF) || SCB.initialized(toTF))
				NW_SAT_constraints.emplace_back(2);
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 2, 0);
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 1);

				//these predicates are constructed to "reset" the stateElement's initialized flag if "any" of the above conditions hadn't been fulfilled!!
				//(SCB.cond_A(fromTF) || SCB.initialized(fromTF) || !SCB.initialized(toTF)) ^ (SCB.cond_A_initialized(fromTF) || SCB.initialized(fromTF) || !SCB.initialized(toTF)) ^ (SCB.cond_B(fromTF) || SCB.initialized(fromTF) || !SCB.initialized(toTF)) ^ (SCB.cond_B_initialized(fromTF) || SCB.initialized(fromTF) || !SCB.initialized(toTF))
				
				//First loop for: basic_constraints
				for (size_t j = 0, e2 = NW_stateElements[i].basic_const.size(); j < e2; j++)
				{
					NW_SAT_constraints.emplace_back(3);											//(SCB.cond_A_initialized(fromTF) || SCB.initialized(fromTF) || !SCB.initialized(toTF))
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 2, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 2, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 0); 
					
					NW_SAT_constraints.emplace_back(3);											//(SCB.cond_A(fromTF) || SCB.initialized(fromTF) || !SCB.initialized(toTF))
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 1, NW_stateElements[i].basic_const[j].state);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 2, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 0);
				}
				//Second loop for: supplementary_constraints
				for (size_t j = 0, e2 = NW_stateElements[i].supp_const.size(); j < e2; j++)
				{
					NW_SAT_constraints.emplace_back(3);											//(SCB.cond_A_initialized(fromTF) || SCB.initialized(fromTF) || !SCB.initialized(toTF))
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 2, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 2, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 0);
					
					NW_SAT_constraints.emplace_back(3);											//(SCB.cond_A(fromTF) || SCB.initialized(fromTF) || !SCB.initialized(toTF))
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 1, NW_stateElements[i].supp_const[j].state);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 2, 1);
					NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 0);
				}
			}
			else
			{
				//for Always-Active scan registers, it have to be initialized instantly and in every transition timeframe, as it is always part of the Active scan path.
				NW_SAT_constraints.emplace_back(1);  //condition: Flag(toTF) 
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 1);
				
				/*
				//No need for adding these predicates where for "always-active" SCBs they can't be UN-initialized in any time frame by nature.
				//these predicates are constructed to "set" the stateElement's initialized flag based on the validation of "any" of the actiavtion conditions or not
				NW_SAT_constraints.emplace_back(2);  //condition: (SCB(toTF)^Flag(toTF) || !SCB(toTF)^Flag(toTF)) --> (!SCB(toTF) || Flag(toTF)) ^ (SCB(toTF) || Flag(toTF))
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 1);
				NW_SAT_constraints.emplace_back(2);  //(SCB(toTF) || Flag(toTF))
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
				NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 1);

				//these predicates are constructed to "set" the stateElement's flag based on previous time frame flag's state
				NW_SAT_predicates.emplace_back(2);  //(!flag(fromTF) || Flag(toTF))
				NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 2, 0);
				NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 1);

				//these predicates are constructed to "reset" the stateElement's flag, if "all" of the above conditions hadn't been fulfilled!!
				NW_SAT_predicates.emplace_back(4); // needs (4) for: (SCB(toTF) || !SCB(toTF) || flag(fromTF) || !flag(TF))
				NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 1);
				NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 1, 0);
				NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 2, 1);
				NW_SAT_predicates.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 0);
				*/
			}
		}
	}
}

void SCT_vertex::ConfiguredSignal_monitoring_constraints_for_anyInitialConfiguration(unsigned int fromTF, unsigned int toTF)
{
	//Configured flag is used to indicate that (any_target) configuration is reached, since now we haven't a (specific) target_state to use, we use the Configured_flag.
	//to set this flag to true we need to check the satisfying of each of : 1) set of basic dependencies. 2) set of supplementary dependencies. 3) set of dependant SCBs
	//There is no need to append this condition (if (NW_stateElements[i].relevancy)), as this flag is applied on all network SCBs
	unsigned int basicConst_size, suppConst_size;

	for (size_t i = 0, e1 = NW_stateElements.size(); i < e1; i++)
	{
		NW_SAT_variables.emplace_back(NW_stateElements[i].id, toTF, 3, SATvariable_no++);
		NW_SAT_constraints.emplace_back((NW_stateElements[i].basic_const.size() * 2) + (NW_stateElements[i].supp_const.size() * 2) + NW_stateElements[i].DSR.size() + 1);	//(*2): one for the (state) variable and another one for the (initialized_flag) variable associated with previous time frame or (fromTF). another incremental is added foe supplementary constraints. (+ DSR.size()) for DSRs. (+1): for the initialized_flag(toTF) literal.
		
		if (NW_stateElements[i].basic_const[0].clause == "TRUE")
		{
			basicConst_size = 0;
			suppConst_size = 0;
		}
		else
		{
			basicConst_size = NW_stateElements[i].basic_const.size();
			suppConst_size = NW_stateElements[i].supp_const.size();
		}

		//these predicates are constructed to "set" the stateElement's (configured flag) based on the validation of "all" actiavtion conditions or not. {BC + SC + DSR}
		//(!cond_A(fromTF) || !cond_A_initialized(fromTF) || !cond_B(fromTF) || !cond_B_initialized(fromTF) || .. || SCB.configured(toTF))
		//First loop: to append the satisfying of the basic constraints
		for (size_t j = 0; j < basicConst_size; j++)
		{
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 2, 0); //(0) means !initialized_flag.
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 1, !NW_stateElements[i].basic_const[j].state);
		}
		//Second loop to append Supplementary Constraints
		for (size_t j = 0; j < suppConst_size; j++)
		{
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 2, 0); //(0) means !initialized_flag.
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 1, !NW_stateElements[i].supp_const[j].state);
		}
		//Third loop to the Dependent-Scan-Registers (DSR) 
		for (size_t j = 0, e2 = NW_stateElements[i].DSR.size(); j < e2; j++)
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].DSR[j], toTF, 3, 0); //(0) means !configured_flag for all DSR.
			
		NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 3, 1);

		//these predicates are constructed to "set" the stateElement's flag based on previous time frame flag's state. So that if the configured_flag for this SCB was already set through any previous time frames, then its state stable at the "same_fired_state".  
		//(!SCB.configured(fromTF) || SCB.configured(toTF))
		NW_SAT_constraints.emplace_back(2);
		NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 3, 0);
		NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 3, 1);

		//these predicates are constructed to "reset" the stateElement's configured flag if "any" of the above conditions hadn't been fulfilled!!
		//(SCB.cond_A(fromTF) || SCB.configured(fromTF) || !SCB.configured(toTF)) ^ (SCB.cond_A_initialized(fromTF) || SCB.configured(fromTF) || !SCB.configured(toTF)) ^ (SCB.cond_B(fromTF) || SCB.configured(fromTF) || !SCB.configured(toTF)) ^ (SCB.cond_B_initialized(fromTF) || SCB.configured(fromTF) || !SCB.configured(toTF)) ^ for every new condition.
		//First loop for: basic_constraints
		for (size_t j = 0; j < basicConst_size; j++)
		{
			NW_SAT_constraints.emplace_back(3);			//(SCB.cond_A_initialized(fromTF) || SCB.configured(fromTF) || !SCB.configured(toTF))
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 2, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 3, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 3, 0);
			
			NW_SAT_constraints.emplace_back(3);			//(SCB.cond_A(fromTF) || SCB.configured(fromTF) || !SCB.configured(toTF))
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].basic_const[j].clause, fromTF, 1, NW_stateElements[i].basic_const[j].state);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 3, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 3, 0);
		}
		//Second loop for: supplementary_constraints
		for (size_t j = 0; j < suppConst_size; j++)
		{
			NW_SAT_constraints.emplace_back(3);		   //(SCB.cond_A_initialized(fromTF) || SCB.configured(fromTF) || !SCB.configured(toTF))
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 2, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 2, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 2, 0);
			
			NW_SAT_constraints.emplace_back(3);		   //(SCB.cond_A(fromTF) || SCB.configured(fromTF) || !SCB.configured(toTF))
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].supp_const[j].clause, fromTF, 1, NW_stateElements[i].supp_const[j].state);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 3, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 3, 0);
		}
		//Third loop for: DSR
		for (size_t j = 0, e2 = NW_stateElements[i].DSR.size(); j < e2; j++)
		{
			NW_SAT_constraints.emplace_back(3);		   //(DSR.configured(toTF) || SCB.configured(fromTF) || !SCB.configured(toTF))
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].DSR[j], toTF, 3, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, fromTF, 3, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 3, 0);
		}
		

		if ((basicConst_size == 0) && (NW_stateElements[i].DSR.size() == 0))
		{
			//for Always-Active scan registers, it have to be configured instantly if it was independant by any network SCB
			NW_SAT_constraints.emplace_back(1);  //condition: Flag(toTF) 
			NW_SAT_constraints.back().SAT_literals.emplace_back(NW_stateElements[i].id, toTF, 3, 1);
		}
	}
}

void SCT_vertex::target_configuration_constraints()
{
	unsigned int Active_TFs = 0; //refers to the number of time frames that should be active in case of write and read access requets.
	unsigned int target_reg_index = get_selection_clause_index(NW_TDRs.back().reg_id);

	delete_threshold = NW_SAT_constraints.size(); //here we update the Read/Write threshold associated with the current time frame. So that, if no solution was found we could unroll back all the SAT_preducates associated with the previous time frame. 

	if (Active_ReadWrite_access) //For "Active" requests
		Active_TFs = no_timeFrames;  //in Active Access: SAT Solver stops "once" the target_reg's structural dependencies becomes satisfied and therefore the target_reg would be Active during the following time frame.
	else if (no_timeFrames > 0)//For "Read/Write Access"
		Active_TFs = no_timeFrames - 1;	//in Read/Write Access: Retargeting stops "after" at least one cycle from putting the target_reg on the ASP, i.e. the target_reg should becomes Active before the final_CSU by at least by one time frame to satisfy the read or write requests through the *last* time frame, that's why we write (no_timeFrames - 1).

	if (NW_selectElements[target_reg_index].basic_const[0].clause != "TRUE") //if this is the case, then the target_reg is already part of the ASP and the SAT problem is originally  SATISFIABLE.
	{
		for (size_t i = 0, e = NW_selectElements[target_reg_index].basic_const.size(); i < e; i++)  //looping on the literals of the selection clause of the target_reg to make sure they all satisfied for the purpose of the Read/ Write Requests.
			NW_SAT_constraints.emplace_back(NW_selectElements[target_reg_index].basic_const[i].clause, Active_TFs, 1, NW_selectElements[target_reg_index].basic_const[i].state); //"state" associated to each tareget_reg's selection clause, for EX: Active(I2)= SCB1 ^ !SCB3
	}
}

void SCT_vertex::target_configuration_constraints_for_anyInitialConfiguration(vector<_clause>& basic_const, vector<_clause>& supplemental_const)
{
	//This is used within the Upper-Bound Computain problems: As we loop on the (basic_const) and (supplemental_const) of the {set} of target configurations
	//for (UBC) problems we seek for the max no_CSUs to put the target_reg on the ASP, i.e. make the target_reg *Active* by satisfying all of its (structural dependencies + Target_state constraints); That's why we follow (Active) requests' (same) rules in determining the Active_TFs.
	unsigned int Active_TFs = no_timeFrames;  //Since we define the UB as the maximum no. of CSUs to activate the TDR and not to read/write over it.
	unsigned int target_reg_index = get_selection_clause_index(NW_TDRs.back().reg_id);

	delete_threshold = NW_SAT_constraints.size(); //here we update the Read/Write threshold associated with the current time frame. So that, if no solution was found we could unroll back all the SAT_preducates associated with the previous time frame. 

	if (UB_Model != 3)
	{
		if (NW_selectElements[target_reg_index].basic_const[0].clause != "TRUE") //no constraints to add it if the TDR was already active
		{
			//First loop for: Basic_constraints
			for (size_t i = 0, e = basic_const.size(); i < e; i++)  //looping on the literals of the selection clause of the target_reg to make sure they all satisfied for the purpose of the Read/ Write Requests.
			{
				NW_SAT_constraints.emplace_back(basic_const[i].clause, Active_TFs, 2, 1); //this is needed, where for (UBC) the network starts from (unkown, unInitialized) state. So, this predicate insures that the SCB.state was also initialized and opened.
				NW_SAT_constraints.emplace_back(basic_const[i].clause, Active_TFs, 1, basic_const[i].state); //"state" associated to each tareget_reg's selection clause, for EX: Active(I2)= SCB1 ^ !SCB3	
			}
			//Second loop for: Supplementary_constraints
			for (size_t i = 0, e = supplemental_const.size(); i < e; i++)  //looping on the literals of the selection clause of the target_reg to make sure they all satisfied for the purpose of the Read/ Write Requests.
			{
				NW_SAT_constraints.emplace_back(supplemental_const[i].clause, Active_TFs, 2, 1); //this is needed, where for (UBC) the network starts from (unkown, unInitialized) state. So, this predicate insures that the SCB.state was also initialized and opened.
				NW_SAT_constraints.emplace_back(supplemental_const[i].clause, Active_TFs, 1, supplemental_const[i].state); //"state" associated to each tareget_reg's selection clause, for EX: Active(I2)= SCB1 ^ !SCB3	
			}
		}
	}
	else //for (NW_UB) we need to insure that the (Configured) flags of NW_SCBs are all fired.
		any_target_configuration_constraints_for_lastTF(); //true means for "last" time frame
}

void SCT_vertex::convert_constraints_to_CNF()
{
	string CNF_clause, negation;

	//First we need to clear the old SAT problem in case of any and we replace it with the new one. (new SAT instance could represents the "same" retargeting/UBC problem but using "more" number of time frames, or it could represents "different" retargeting/UBC problem for another NW_TDR in the same network. That's why we need each time to clear/reset the old instance first.
	if (NW_SAT_clauses.size() == 0)
		NW_SAT_clauses.reserve(NW_SAT_constraints.size() + 1 + NW_TDRs.back().solver_returns.capacity()); //SAT_clauses vector has the same size as SAT_predicates vector; where the only difference between the two vectors is that in SAT_clauses vector we replace each SAT_literal with its corresponding SAT_no, also (+1) to account for the "p cnf " line, (+possibleRetargetings.capacity()) in case the user request the optimal solution, where we have to append to the CNF clauses all the found/possible solutions
	else
		NW_SAT_clauses.clear();

	CNF_clause = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_constraints.size()); //(SATvariable_no - 1) because we use (++) --> SATvariable_no++. 
	NW_SAT_clauses.emplace_back(CNF_clause);

	for (size_t i = 0, e1 = NW_SAT_constraints.size(); i < e1; i++)
	{
		CNF_clause = "";
		for (size_t j = 0, e2 = NW_SAT_constraints[i].SAT_literals.size(); j < e2; j++)
		{
			if (NW_SAT_constraints[i].SAT_literals[0].id != "0") //(== "0") this predicate could be inserted to the SAT problem to indicates that the SAT instance is not satisfiable using this number of time frames
			{
				negation = (NW_SAT_constraints[i].SAT_literals[j].state == 0) ? "-" : "";
				CNF_clause += negation + to_string(get_SATvariable_no(NW_SAT_constraints[i].SAT_literals[j].id, NW_SAT_constraints[i].SAT_literals[j].timeFrame, NW_SAT_constraints[i].SAT_literals[j].type)) + " ";
			}
			if (j == e2 - 1)
				CNF_clause += "0";
		}

		NW_SAT_clauses.emplace_back(CNF_clause);
	}
	NW_TDRs.back().n_SAT_clauses = NW_SAT_clauses.size() - 1; //(-1) to exclude the first line

	//This is a *very important* step for (the optimal *Retargeting* problems): where we need to exclude also all previously obtained solutions from the search space as they were already considered before in our possible retargeting solutions; and this is by incuding their negated_satisfiable_string in our SAT_problem.
	if (optimal_solution && no_CSUs != -1) //(no_CSUs != -1) this is needed to NOT consider the (UBC) problems
	{
		for (unsigned int i = 0, e1 = NW_TDRs.size(); i < e1; i++)
		{
			for (unsigned int j = 0, e2 = NW_TDRs[i].solver_returns.size(); j < e2; j++)
				NW_SAT_clauses.emplace_back(get_negated_string(NW_TDRs[i].solver_returns[j].satisfiable_string));
		}

		//Next update the number of SAT clauses to include the previously examined retargeting solutions also, using the updated size value (NW_SAT_clauses.size()).
		if (NW_SAT_constraints.size() < NW_SAT_clauses.size() - 1) //means a satisfying_assignment solutions have beed added and we need to re-update the no_SAT_clauses. (NW_SAT_clauses.size() - 1): (-1) to unconsider the (p cnf ..) clause.
			NW_SAT_clauses[0] = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_clauses.size() - 1);
	}

	print_file(SAT_clauses, path + "NW_SCT_to_SAT.txt", "w");
}

void SCT_vertex::convert_constraints_to_CNF_withIDs()
{
	NW_SAT_clauses.clear(); //to clear the first CNF clauses created by the previous (convert_predicates_to_CNF) calling.

	string CNF_clause = "\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\";
	NW_SAT_clauses.emplace_back(CNF_clause);
	CNF_clause = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_constraints.size());
	NW_SAT_clauses.emplace_back(CNF_clause);

	for (size_t i = 0, e1 = NW_SAT_constraints.size(); i < e1; i++)
	{
		CNF_clause = "";
		for (size_t j = 0, e2 = NW_SAT_constraints[i].SAT_literals.size(); j < e2; j++)
		{
			if (NW_SAT_constraints[i].SAT_literals[0].id != "0") //(== "0") this predicate could be inserted to the ST problem to indicates that the SAT instance is not satisfiable using this number of time frames
			{
				CNF_clause += (NW_SAT_constraints[i].SAT_literals[j].state == 0) ? "-" : "";
				CNF_clause += (NW_SAT_constraints[i].SAT_literals[j].type == 1) ? "state(" : (NW_SAT_constraints[i].SAT_literals[j].type == 2) ? "initialized(" : "Configured(";
				CNF_clause += NW_SAT_constraints[i].SAT_literals[j].id + ", " + to_string(NW_SAT_constraints[i].SAT_literals[j].timeFrame) + ", " + to_string(get_SATvariable_no(NW_SAT_constraints[i].SAT_literals[j].id, NW_SAT_constraints[i].SAT_literals[j].timeFrame, NW_SAT_constraints[i].SAT_literals[j].type)) + ") ";
			}
			if (j == e2 - 1)
				CNF_clause += "0";
		}

		NW_SAT_clauses.emplace_back(CNF_clause);
	}

	// here we append "a" to the original SAT_clauses, the same SAT_clauses but writen in meaningful or understandable way!!
	print_file(SAT_clauses, path + "NW_SCT_to_SAT.txt", "a");
}

bool SCT_vertex::is_SAT_instance_satisfiable()
{
	//1- run the SAT_solver on the updated (SAT_problem), updated with other found solutions in case of optimal_retargeting active choice.
	run_SAT_solver_withNoPrint(path + "NW_SCT_to_SAT.txt", NW_TDRs.back().solver_returns.back());
	if (NW_TDRs.back().solver_returns.back().n_conflicts > 0)
		printf("\nSAT solver has conflicts = %d, while retargeting (%s)\n", NW_TDRs.back().solver_returns.back().n_conflicts, NW_TDRs.back().reg_id.c_str());

	if (NW_TDRs.back().solver_returns.back().satisfiable_string.length() != 0) //means the problem is "SATISFIABLE"
	{
		//2- assign the currently used number of time frames to the SAT solutionn we just got.
		NW_TDRs.back().solver_returns.back().no_CSUs = no_timeFrames;

		//3- set (SAT_assignment) values returned by the SAT solver for each SAT vertex in the network, this operation should be applied on each time frame.
		map_SATAssignmentSolution_to_SATvariables();

		//4- Generate Active Scan Path associated with each time frame.
		generate_output_retargeting_vector();

		//5- Compute the number of clock cycles for the Retargeting_Solution associated with the current satisfiable_string;
		compute_no_clockCycles();

		//6- Generate NW "retargeting" output vectors which should be entered to the TAP controller to read/write the value in the target_reg.
		print_file(SAT_retargeting_vectors, path + "NW_SCT_to_SAT_retargeting_vectors.txt", "a");

		return true;
	}
	else
	{
		//7- Don't Remove the returned solution from (NW_TDRs.back().solver_returns) vector even if the SAT problem was UNSATISFIABLE, i.e. it has no (assignment_solution) using the assigned number of time frames; because we need to consider this solution's execution_time within the "total" SAT_Solving_time.
		//NW_TDRs.back().solver_returns.erase(NW_TDRs.back().solver_returns.end() - 1);
		return false;
	}
}

void SCT_vertex::compute_no_clockCycles()
{
	unsigned int no_clkCycles = 0;

	for (size_t i = 0, e1 = SAT_output.size(); i < e1; i++)
	{
		for (size_t j = 0, e2 = SAT_output[i].size(); j < e2; j++)
		{
			no_clkCycles += (is_SCB(SAT_output[i][j].clause)) ? 1 : get_length(SAT_output[i][j].clause);//where all NW_SCBs have a length of (1) bit.
		}

		no_clkCycles += 2; //(+2) for the update and capture operations.
	}

	NW_TDRs.back().solver_returns.back().AccessTime = no_clkCycles;
}

void SCT_vertex::generate_output_retargeting_vector()
{
	//To find the scan-in data for the primary scan input of a network in the i-th CSU operation, the network’s graph is traversed along the active scan path of frame i − 1. The content of visited scan segments is acquired from the i-th time frame of the satisfying assignment.
	//so ASP can be concluded from the sel() value of time frame (TF).
	//while constent of ASP can be infered from the state() value of time frame (TF+1).

	unsigned int TF = 0;
	unsigned int sat_assignment;
	unsigned int NW_size = NW_stateElements.size() + NW_selectElements.size();

	//reserve space for the "initial" Time Frame
	SAT_output.emplace_back(); //this constructor is used with any two dimentional vector, where this emplace_back() is used with the outer vector to initialize and reserve the internal vector capacity.
	SAT_output.back().reserve(NW_size); //this is the max that all NW state elements and NW shift registers are part of the ASP.

	if (no_timeFrames > 0)
	{
		for (size_t index = 0, e = NW_SAT_variables.size(); index < e; index++) //NW_SAT_variables represent the variables in the SCT in each TF, so, we need to include "other" NW_SCBs and "all" NW_TDRs which are not in the SCT, however they could be part of the ASP.
		{
			if (NW_SAT_variables[index].timeFrame == TF)
			{
				if (is_Active_SCB(NW_SAT_variables[index].id, NW_SAT_variables[index].timeFrame))	//construct Active Scan Path (ASP) each time frame, by concatenating all active state elements through the "same" time frame. So we check if this SAT_varaible is Active at this TF or not. //the returning index belonging to (NW_stateElements) because we are looping on (NW_SAT_variables) which constructed from (NW_stateElements).
				{
					if (TF < no_timeFrames)
					{
						sat_assignment = get_SATvariable_assignment(NW_SAT_variables[index].id, TF + 1, NW_SAT_variables[index].type); //(TF+1) b/c I want the content/state of the scan segment from the next TF of the satisfying assignmnet after identifying that it is Active. 
						SAT_output.back().emplace_back(NW_SAT_variables[index].id, sat_assignment);
					}
					else //if(TF  == no_timeFrames). for the last TF, we need to consider only the (select) variable, which would be used in generating the last ASP, and hence to be considered while computing the number of cycles associated with each retargeting solution.
						SAT_output.back().emplace_back(NW_SAT_variables[index].id, -1);
				}
			}
			else
			{
				//Before moving to the next time frame we need to generate also the "select" state of other NW_SCBs which were not part of the SCT and also all network "TDRs/Shift_Registers"; because they could be also part of the ASP.
				set_ASP_for_variables_outside_SearchSpace(TF);

				//Now we could move to the next TF:
				if ((TF + 1) == no_timeFrames)	//this is a stoping condition where we don't need the "select" state or the ASP for the timeFrames which come after the entered no of time frames.
					break;

				TF++;
				index--; //to "Recheck" on that SAT_variable (NW_SAT_variables[i].timeFrame) after updating the time frame slot associated with the next CSU output vector.

				//reserve space for the the "next" Time Frame
				SAT_output.emplace_back();
				SAT_output.back().reserve(NW_size);
			}
		}
	}
	else //in case (TF==0), generate the output from the "initial_configuration" input, where the (target_reg) is *already* Active and accessable with no need for any retargetig vectors to put it on the ASP.
	{
		bool active;
		for (size_t i = 0, e1 = NW_stateElements.size(); i < e1; i++) //for NW_SCBs not in the SCT
		{
			active = true;
			if (NW_stateElements[i].basic_const[0].clause != "TRUE")
			{
				for (size_t j = 0, e2 = NW_stateElements[i].basic_const.size(); j < e2; j++) //for NW_SCBs not in the SCT
				{
					if (NW_stateElements[i].basic_const[j].state != initial_configuration)
					{
						active = false;
						break;
					}
				}
			}
			if (active)
				SAT_output.back().emplace_back(NW_stateElements[i].id, initial_configuration);
		}
		for (size_t i = 0, e1 = NW_selectElements.size(); i < e1; i++) //for NW_SCBs not in the SCT
		{
			active = true;
			if (NW_selectElements[i].basic_const[0].clause != "TRUE")
			{
				for (size_t j = 0, e2 = NW_selectElements[i].basic_const.size(); j < e2; j++) //for NW_SCBs not in the SCT
				{
					if (NW_selectElements[i].basic_const[j].state != initial_configuration)
					{
						active = false;
						break;
					}
				}
			}
			if (active)
				SAT_output.back().emplace_back(NW_selectElements[i].id, -1); //(-1) means (UNKOWN) state, where the shift_register's "state" value is assumed to be unkown we only predict its "select" state if it is Active or not through each TF.
		}
	}
}

void SCT_vertex::print_file(_SAT_Type option, const string& file_name, const string& file_opening_option)
{
	FILE *file;
	string output_text = "";

	if ((file = fopen(file_name.c_str(), file_opening_option.c_str())) != NULL) //"a" for append or "w" for write.
	{
		switch (option)
		{
		case SAT_clauses:
		{
			/*
			The first non-comment line must be of the form:
			p cnf NUMBER_OF_VARIABLES NUMBER_OF_CLAUSES
			Each of the non-comment lines afterwards defines a clause.
			Each of these lines is a space-separated list of variables.
			a positive value means that corresponding variable (so 4 means x4),
			and a negative value means the negation of that variable (so -5 means -x5).
			Each line must end in a space and the number 0.
			EX:
			p cnf 5 3
			1 -5 4 0
			*/

			for (size_t i = 0, e = NW_SAT_clauses.size(); i < e; i++)
				output_text += NW_SAT_clauses[i] + "\n";

			break;
		}
		case SAT_retargeting_vectors:
		{
			output_text = "The Retaregeting output vectors for (" + NW_TDRs.back().reg_id + ") using (" + to_string(no_timeFrames) + " CSUs) is: \n";
			//output_text += satisfiable_string + "\n";

			for (unsigned int i = 0, e1 = SAT_output.size(); i < e1; i++)
			{
				output_text += "ASP for TF(" + to_string(i) + ") is: ";
				for (unsigned int j = 0, e2 = SAT_output[i].size(); j < e2; j++)
				{
					output_text += SAT_output[i][j].clause + " = ";
					if (SAT_output[i][j].state != -1)
						output_text += to_string(SAT_output[i][j].state) + ", ";
					else
						output_text += "X, ";  //"X" for unknown.
				}
				output_text += "\n";
			}

			output_text += "Number of Clock Cycles = " + to_string(NW_TDRs.back().solver_returns.back().AccessTime) + "\n"; //(no_CSUs == 0) if the TDR was already included into the ASP
			output_text += "/////////////////////////////////////////////////////////////////////////////\n";
			break;
		}
		}
		fprintf(file, "%s", output_text.c_str());
		fclose(file);
	}
	else printf("%s \n", "Unable to open file");
}

void SCT_vertex::print_vectors_size_capacity_comparison()
{
	FILE *file;
	string file_name = path + "NW_vectors_sizes.txt";

	if ((file = fopen(file_name.c_str(), "a")) != NULL)	// use "a" for append, "w" to overwrite, previous content will be deleted. https://stackoverflow.com/questions/2393345/how-to-append-text-to-a-text-file-in-c
	{
		fprintf(file, "\n//////////////////////////FOR SCT_to_SAT//////////////////////////\n");
		fprintf(file, "SAT_predicates: Size= %lu, \t Capacity= %lu\n", NW_SAT_constraints.size(), Expected_no_constraints); //where size_t and .size() are of type: long unsigned int (https://stackoverflow.com/questions/4033018/how-to-print-an-unsigned-long-int-with-printf-in-c/4033039)
		fprintf(file, "SAT_clauses: Size= %lu, \t Capacity= %lu\n", NW_SAT_clauses.size(), NW_SAT_clauses.capacity());  //they should be equal. So, we can detect if enlarging in vector's capacity occurs by checking if (Capacity_before == Size_After) or not. 
		fprintf(file, "SAT_variables: Size= %lu, \t Capacity= %lu\n", NW_SAT_variables.size(), Expected_no_SATvariables);
		fprintf(file, "////////////////////////////////////////////////////////////////////////////////////\n");

		fclose(file);
	}
	else printf("%s \n", "Unable to open pdl file");
}

void SCT_vertex::print_NWstatistics(bool target_statistics, unsigned int index)
{
	//statistics for specific "target_reg"
	if ((target_statistics) && (NW_TDRs[index].solver_returns.size() > 0)) //(NW_TDRs[index].solver_returns.size() > 0) check if there exist a retargeting solution or not!!
	{
		printf("\n//////////////////////////////////////////////////////////////////");
		printf("\n*******For %s: *******\n", NW_TDRs[index].reg_id.c_str());
		printf("\nFor SAT_problem size : #variables = %lu, #clauses = %lu", NW_TDRs[index].n_SAT_variables, NW_TDRs[index].n_SAT_clauses);
		printf("\nNumber of Conflicts = %f", get_avg('C'));
		printf("\nInstrument Access Time = %f", get_avg('A'));
		printf("\nRetargeting took %f s", get_avg('E'));

		printf("\n\n//////////////////////////////////////////////////////////////////\n");
	}

	//statistics for the "whole" NW	
	else if (NW_TDRs[index].solver_returns.size() > 0)
	{
		printf("\n//////////////////////////////////////////////////////////////////");

		printf("\nNumber of TDR's = %d", NW_TDRs.size());
		printf("\nFor SAT_problem size : \n\t#vars_Avg/#clauses_Avg = %f/%f, #vars_Max/#clauses_Max = %f/%f", get_avg('V'), get_avg('L'), get_max('V'), get_max('L'));
		printf("\nFor Conflicts NW parameter:\n\tAvg= %f, Max= %f", get_avg('C'), get_max('C'));
		printf("\nFor Access time(CC) NW parameter:\n\tAvg= %f, Max= %f", get_avg('A'), get_max('A'));
		printf("\nFor Execution time(sec) NW parameter:\n\tAvg= %f, Max= %f", get_avg('E'), get_max('E'));

		printf("\n//////////////////////////////////////////////////////////////////\n");
	}
}

unsigned int SCT_vertex::get_length(const string& id)
{
	for (size_t i = 0, e = NW_selectElements.size(); i < e; i++)
	{
		if (NW_selectElements[i].id == id)
			return NW_selectElements[i].length;
	}
}

string SCT_vertex::get_negated_string(const string& input)
{
	istringstream SAT_assignment(input);
	string token, SAT_variable, negated_staisfiable_str = "";
	unsigned int itr;
	bool is_negated;

	while (getline(SAT_assignment, token, ' '))
	{
		is_negated = false;
		itr = 0;
		SAT_variable = "";

		if (token[0] != '-')
			SAT_variable = token + " ";
		else
		{
			is_negated = true;
			itr++;// ignore the sign from the SAT_no
			while (token[itr] != '\0')
				SAT_variable += token[itr++];

			SAT_variable += " ";
		}

		negated_staisfiable_str += is_negated ? SAT_variable : "-" + SAT_variable; //invert the assignment value to exclude this assignment_solution from the next possible_retaregeting
	}
	negated_staisfiable_str += "0"; //where each CNF clause should end with "0".

	return negated_staisfiable_str;
}

unsigned int SCT_vertex::get_selection_clause_index(const string& node_id)
{
	if (is_SCB(node_id))
	{
		for (unsigned int index = 0, e = NW_stateElements.size(); index < e; index++)
		{
			if (NW_stateElements[index].id == node_id)
				return index;
		}
	}
	else //in case we look for the selection clause of a NW_TDR.
	{
		for (unsigned int index = 0, e = NW_selectElements.size(); index < e; index++)
		{
			if (NW_selectElements[index].id == node_id)
				return index;
		}
	}
}

unsigned int SCT_vertex::get_SATvariable_no(const string& id, unsigned int timeFrame, unsigned int type)
{
	//For "SCT_to_SAT" implementation, Key=(id, type, timeFrame)
	//To speed up searching in (NW_SAT_variables) we use 'search_range' variable to search on SATvariable_no within specific/limited range and not looping on the "whole" range of NW_SAT_variables.
	unsigned int start, stop;
	start = index_range[timeFrame];
	stop = (timeFrame < no_timeFrames) ? index_range[timeFrame + 1] : NW_SAT_variables.size(); //(<) condition is more generic than (!=) condition, where (!<) will include (== and >) in one common side.

	for (unsigned int index = start; index < stop; index++)
	{
		if ((NW_SAT_variables[index].id == id) && (NW_SAT_variables[index].type == type))
			return NW_SAT_variables[index].SAT_no;
	}

	printf("SAT_variable doesn't exist !!\n");
	exit(0); //if SAT_variable doesn't exist
}

void SCT_vertex::set_SATvariable_assignment(unsigned int SAT_no, bool SAT_value)
{
	//first loop is used to set the SAT_variable to the correct group of SAT_variables which exist in the same time frame, to speed up the search and not to be through the whole NW_SAT_variables range.
	unsigned int TF, startIndexOf_fittingTF, stopIndexOf_fittingTF = 0; //(0) means unitialized yet;
	for (TF = 1; TF <= no_timeFrames; TF++)
	{
		if (SAT_no <= index_range[TF])
		{
			startIndexOf_fittingTF = index_range[TF - 1];
			stopIndexOf_fittingTF = index_range[TF];
			break;
		}
	}
	if (stopIndexOf_fittingTF == 0) //(stopIndexOf_fittingTF == 0) means still not initialized yet !!
	{
		startIndexOf_fittingTF = index_range[TF - 1];
		stopIndexOf_fittingTF = NW_SAT_variables.size();
	}

	for (unsigned int index = startIndexOf_fittingTF; index <= stopIndexOf_fittingTF; index++) //only search betwean (start_index, stop_index)
	{
		if (NW_SAT_variables[index].SAT_no == SAT_no)
		{
			NW_SAT_variables[index].SAT_assignment = SAT_value;
			return;
		}
	}

	printf("SAT_variable doesn't exist !!\n");
	exit(0); //if SAT_variable doesn't exist
}

unsigned int SCT_vertex::get_SATvariable_assignment(const string& id, unsigned int timeFrame, unsigned int type)
{
	//To speed up searching in (NW_SAT_variables) we use 'search_range' variable to search on SATvariable_no within specific/limited range and not looping on the "whole" range of NW_SAT_variables.
	unsigned int start, stop;
	start = index_range[timeFrame];
	stop = (timeFrame < no_timeFrames) ? index_range[timeFrame + 1] : NW_SAT_variables.size();

	for (unsigned int index = start; index < stop; index++)
	{
		if ((NW_SAT_variables[index].id == id) && (NW_SAT_variables[index].type == type))
			return NW_SAT_variables[index].SAT_assignment;
	}

	printf("SAT_variable doesn't exist !!\n");
	exit(0); //"Means it doesn't exist; so, I should throw here an error also.
}

void SCT_vertex::map_SATAssignmentSolution_to_SATvariables() //extract SAT_assignment values from the "SATISFIABLE" string
{
	istringstream SAT_assignment(NW_TDRs.back().solver_returns.back().satisfiable_string);
	string token, SAT_variable;
	unsigned int itr;
	bool SAT_value;

	while (getline(SAT_assignment, token, ' '))
	{
		SAT_value = true;
		itr = 0;
		SAT_variable = "";

		if (token[0] != '-')
			SAT_variable = token;
		else
		{
			SAT_value = false;
			itr++;// ignore the sign from the SAT_variable
			while (token[itr] != '\0')
				SAT_variable += token[itr++];
		}

		set_SATvariable_assignment(stoi(SAT_variable), SAT_value);
	}
}

bool SCT_vertex::is_Active_SCB(const string& reg_id, unsigned int TF)
{
	//This section is used to generate the select state for each element in the network using its selection clause. By checking if element's selection clause is satisfied through the passed (TF) and hence the element is Active or not.
	unsigned int SATvariable_assignment = 0;
	unsigned int reg_index = get_selection_clause_index(reg_id);
	
	if (NW_stateElements[reg_index].basic_const[0].clause != "TRUE")
	{
		for (size_t i = 0, e1 = NW_stateElements[reg_index].basic_const.size(); i < e1; i++)
		{
			for (size_t j = 0, e2 = NW_stateElements.size(); j < e2; j++)
			{
				if (NW_stateElements[j].id == NW_stateElements[reg_index].basic_const[i].clause)
				{
					if (NW_stateElements[j].relevancy)
						SATvariable_assignment = get_SATvariable_assignment(NW_stateElements[reg_index].basic_const[i].clause, TF, 1);
					else
						SATvariable_assignment = NW_stateElements[j].reset_value; //where in SCT model, we set any SCB outside the SCT to the "reset_state"
					break;
				}
			}

			if (NW_stateElements[reg_index].basic_const[i].state != SATvariable_assignment) //We need to check if the reg's selection clauses are satisfied within the "same" state element's time frame. We need to compare the "satisfying-value" of each SCB in the selection_clause with the SAT_assginment value for that "state" variable in the corresponding time frame, since we compare the satisfying and SAT_assignment values of the (state) variables; we use the value of (1) <-> (state-variable).
				return false;
		}
	}
	
	return true; //if "all" the literals/children in the selection clause are satisfiable through the same (TF), then the node itself is Active.
}

bool SCT_vertex::is_Active_TDR(unsigned int selection_clause_index, unsigned int TF)
{
	//This section is used to generate the select state for each element in the network using its selection clause. By checking if element's selection clause is satisfied through the passed (TF) and hence the element is Active or not.
	unsigned int SATvariable_assignment = 0;
	
	if (NW_selectElements[selection_clause_index].basic_const[0].clause != "TRUE")
	{
		for (size_t i = 0, e1 = NW_selectElements[selection_clause_index].basic_const.size(); i < e1; i++)
		{
			for (size_t j = 0, e2 = NW_stateElements.size(); j < e2; j++)
			{
				if (NW_stateElements[j].id == NW_selectElements[selection_clause_index].basic_const[i].clause)
				{
					if (NW_stateElements[j].relevancy)
						SATvariable_assignment = get_SATvariable_assignment(NW_selectElements[selection_clause_index].basic_const[i].clause, TF, 1);
					else
						SATvariable_assignment = NW_stateElements[j].reset_value; //where in SCT model, we set any SCB outside the SCT to the "reset_state"
					break;
				}
			}

			if (NW_selectElements[selection_clause_index].basic_const[i].state != SATvariable_assignment) //We need to check if the reg's selection clauses are satisfied within the "same" state element's time frame. We need to compare the "satisfying-value" of each SCB in the selection_clause with the SAT_assginment value for that "state" variable in the corresponding time frame, since we compare the satisfying and SAT_assignment values of the (state) variables; we use the value of (1) <-> (state-variable).
				return false;
		}
	}

	return true; //if "all" the literals/children in the selection clause are satisfiable through the same (TF), then the node itself is Active.
}

bool SCT_vertex::is_SCB(const string& id)
{
	if ((id.find("SR") != std::string::npos) || (id.find("SCB") != std::string::npos))
		return true;

	return false;
}

void SCT_vertex::set_ASP_for_variables_outside_SearchSpace(unsigned int TF)
{
	for (size_t index = 0, e = NW_stateElements.size(); index < e; index++) //for NW_SCBs which are not in the SCT
	{
		if (!NW_stateElements[index].relevancy)
		{
			if (is_Active_SCB(NW_stateElements[index].id, TF))
				SAT_output.back().emplace_back(NW_stateElements[index].id, initial_configuration);
		}
	}
	for (size_t index = 0, e = NW_selectElements.size(); index < e; index++) //for NW_TDRs
	{
		if (is_Active_TDR(index, TF))  //check if any of them are Active through the selected TF or not.
			SAT_output.back().emplace_back(NW_selectElements[index].id, -1); //(-1) means (UNKOWN) state, where the shift_register's "state" value is assumed to be unkown we only predict its "select" state if it is Active or not through each TF.
	}
}

void SCT_vertex::set_longest_AccessMerged_configuration(unsigned int TDR_index, vector<string>& Traversed_TDRs, vector<_clause>& output_accessMerged_configuration)
{
	Traversed_TDRs.emplace_back(NW_selectElements[TDR_index].id); //because it is an "initaitor" for the construction of Access Merged paths. It means that it was not been examined anytime before.
	for (unsigned int n = 0, e = NW_selectElements[TDR_index].basic_const.size(); n < e; n++) //here we set "initially" the TReg's Selection_Clause with the *unvisited-before* TDR's Selection_Clause.
		output_accessMerged_configuration.emplace_back(NW_selectElements[TDR_index].basic_const[n].clause, NW_selectElements[TDR_index].basic_const[n].state);

	for (unsigned int i = 0, e = NW_selectElements.size(); i < e; i++)
	{
		if (i != TDR_index && NW_selectElements[i].basic_const[0].clause != "TRUE")
		{
			if (has_concurrent_access(output_accessMerged_configuration, NW_selectElements[i].basic_const))
			{
				Traversed_TDRs.emplace_back(NW_selectElements[i].id); //we need to append the selected TDR to the set of the traversed nodes.

				//append its selection clause to merge this TDR into the longest access merged path	
				for (unsigned int j = 0, e2 = NW_selectElements[i].basic_const.size(); j < e2; j++)
				{
					if (find(output_accessMerged_configuration.begin(), output_accessMerged_configuration.end(), NW_selectElements[i].basic_const[j].clause) == output_accessMerged_configuration.end()) //I need to include this condition because some literals in the selection clause could be common between multiple TDRs in the same ASP; so, we need to include those common literals for only "once".
						output_accessMerged_configuration.emplace_back(NW_selectElements[i].basic_const[j].clause, NW_selectElements[i].basic_const[j].state);
				}
			}
		}
	}
}

double SCT_vertex::get_avg(char x) //A->access time, C->no of Conflicts, E->execution time
{
	double sum_avg = 0;
	double sum_TDR = 0;

	switch (x) {
	case 'A':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of NW_TDRs that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = NW_TDRs.size(); i < e1; i++)
		{
			if ((e2 = NW_TDRs[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += NW_TDRs[i].solver_returns[j].AccessTime;

				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0; //in case the assigned number of CSUs is not sufficient for the retargetting of any NW_TDR, at then (n_retargeted_TDRs=0)!!
		break;
	}
	case 'C':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of NW_TDRs that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = NW_TDRs.size(); i < e1; i++)
		{
			if ((e2 = NW_TDRs[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += NW_TDRs[i].solver_returns[j].n_conflicts;

				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0;
		break;
	}
	case 'E':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of NW_TDRs that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = NW_TDRs.size(); i < e1; i++)
		{
			if ((e2 = NW_TDRs[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += NW_TDRs[i].solver_returns[j].execution_time;

				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0;
		break;
	}
	case 'V':
	{
		unsigned int i, e;
		for (i = 0, e = NW_TDRs.size(); i < e; i++)
		{
			sum_TDR += NW_TDRs[i].n_SAT_variables;
		}
		return (sum_TDR / e); //e can't be zero; it mus be at least one target_reg!!
		break;
	}
	case 'L':
	{
		unsigned int i, e;
		for (i = 0, e = NW_TDRs.size(); i < e; i++)
		{
			sum_TDR += NW_TDRs[i].n_SAT_clauses;
		}
		return (sum_TDR / e);
		break;
	}
	default: std::printf("Passed parameter isn't valid!!\n"); // no error
		return -1;
		break;
	}
}

double SCT_vertex::get_max(char x)
{
	switch (x) {
	case 'A':
	{
		double max = NW_TDRs[0].solver_returns[0].AccessTime;
		for (size_t i = 0, e1 = NW_TDRs.size(); i < e1; i++)//(i,j) start from (0).
		{
			for (size_t j = 0, e2 = NW_TDRs[i].solver_returns.size(); j < e2; j++)
			{
				if (max < NW_TDRs[i].solver_returns[j].AccessTime)
					max = NW_TDRs[i].solver_returns[j].AccessTime;
			}
		}
		return max;
		break;
	}
	case 'C':
	{
		double max = NW_TDRs[0].solver_returns[0].n_conflicts;
		for (size_t i = 0, e1 = NW_TDRs.size(); i < e1; i++)//(i,j) start from (0).
		{
			for (size_t j = 0, e2 = NW_TDRs[i].solver_returns.size(); j < e2; j++)
			{
				if (max < NW_TDRs[i].solver_returns[j].n_conflicts)
					max = NW_TDRs[i].solver_returns[j].n_conflicts;
			}
		}
		return max;
		break;
	}
	case 'E':
	{
		double max = NW_TDRs[0].solver_returns[0].execution_time;
		for (size_t i = 0, e1 = NW_TDRs.size(); i < e1; i++) //(i,j) start from (0).
		{
			for (size_t j = 0, e2 = NW_TDRs[i].solver_returns.size(); j < e2; j++)
			{
				if (max < NW_TDRs[i].solver_returns[j].execution_time)
					max = NW_TDRs[i].solver_returns[j].execution_time;
			}
		}
		return max;
		break;
	}
	case 'V':
	{
		double max = NW_TDRs[0].n_SAT_variables;
		for (size_t i = 1, e = NW_TDRs.size(); i < e; i++)
		{
			if (max < NW_TDRs[i].n_SAT_variables)
				max = NW_TDRs[i].n_SAT_variables;
		}
		return max;
		break;
	}
	case 'L':
	{
		double max = NW_TDRs[0].n_SAT_clauses;
		for (size_t i = 1, e = NW_TDRs.size(); i < e; i++)
		{
			if (max < NW_TDRs[i].n_SAT_clauses)
				max = NW_TDRs[i].n_SAT_clauses;
		}
		return max;
		break;
	}
	default: printf("Passed parameter isn't valid!!\n"); // no error
		return -1;
		break;
	}
}

void SCT_vertex::set_SupplementaryConstraints(SCT_vertex& target_register)
{
	//this is longest path constraints between (SCBs in the SCT, NW_TDRs): 
	for (size_t index = 0, e = NW_stateElements.size(); index < e; index++)
	{
		if (NW_stateElements[index].relevancy) 
			add_SupplementaryConstraints(NW_stateElements[index]);
	}

	if (UB_Model == 1 || UB_Model == 2 || no_CSUs != -1) //we need to set the supp_const for computing the upper-bound of individual retargeting requests: (UB_Model == 1 || UB_Model == 2)and for the retargeting problem itself (no_CSUs != -1)
		add_SupplementaryConstraints(target_register); //This is to set the Supplemental Constraints of the "target_reg" itself. //this is the longest path constraints between (target_reg, other NW_TDRs), which exists in Model_1 and Model_2 only.
}

void SCT_vertex::add_SupplementaryConstraints(SCT_vertex& node)
{
	unsigned int i, j, e1, e2, controller_index; //this (unsigned int) in spite of the function's argument is (int); because this is would be a correct_setted value of index and we would not neet (-1) for use.
	vector<_clause> CSS; //CSS: common selection set
	CSS.reserve(5); //this is a random picked value

	//this is an optimal condition to stop seeking for LCP in case the passed reg was an "always-Active" reg. //(NW_stateElements[i].clause[0].clause != "TRUE"): this condition to exclude always-active SCBs, since those SCBs are part of any active scan path and "no way" to exclude NW_TDRs without passing through those always-active SCBs.
	if (node.basic_const[0].clause == "TRUE")
		return;

	for (i = 0, e1 = NW_selectElements.size(); i < e1; i++)
	{
		if (NW_selectElements[i].basic_const[0].clause != "TRUE") //For optimality, we ignore always-active NW_TDRs; because there is no way to deActivate them before passing through the configured_SCBs.ASP.
		{
			get_common_selections(node.basic_const, NW_selectElements[i].basic_const, CSS);

			if (!CSS.empty() && has_concurrent_access(node.basic_const, NW_selectElements[i].basic_const))  //First condition: To insure the existence of any dependency between the configured SCB and the network TDR and thus we could try later to break this dependency seeking for optimum retargeting cost . Second condition to insure if the TDR is part of the ASP of any SCB in the SCT or not. (has_concurrent_access) means no conflict. 
			{
				for (j = 0, e2 = NW_selectElements[i].basic_const.size(); j < e2; j++) //here we loop on TDR's controllers seeking for external or separately accessed one.
				{
					controller_index = get_selection_clause_index(NW_selectElements[i].basic_const[j].clause);

					if ((find(CSS.begin(), CSS.end(), NW_stateElements[controller_index].id) == CSS.end()) && (has_separate_access(NW_stateElements[controller_index].basic_const, CSS))) //first condition to insure that the selected controller is not one of the CSS's SCBs. While the other to insure that it can be accessed away from the TDR and the CR from different separate accessed path.
					{
						if (!has_any_dependenceRelation_with_any_relevantSCB(controller_index))
						{
							if (!NW_stateElements[controller_index].relevancy) //if it wasn't set before through the basic network states, then we need to append it along with its structural and tempral dependencies, that's why we invoke the method ()
							{
								NW_stateElements[controller_index].relevancy = true;
								set_relevancy(NW_stateElements[controller_index].basic_const); //this is to append to the search space the set of basic constraints:(structural and temporal) dependencies because of the new added node (the supplemental controller), along with the set of its supplemental dependencies if any.
								add_SupplementaryConstraints(NW_stateElements[controller_index]); //As we have appended the controller's basic constraints, we have to appent its supplemental constraints only.
							}
							node.supp_const.emplace_back(_clause(NW_selectElements[i].basic_const[j].clause, !NW_selectElements[i].basic_const[j].state)); //!state: to enforce the switching off /deAttaching for that TDR.
						}
					}
				}
			}

			CSS.clear();
		}
	}

	vector<_clause>().swap(CSS);
}

void SCT_vertex::get_common_selections(vector<_clause>& sel_clause1, vector<_clause>& sel_clause2, vector<_clause>& output_CSS)
{
	unsigned int index;
	for (unsigned int i = 0, e1 = sel_clause1.size(); i < e1; i++)
	{
		for (unsigned int j = 0, e2 = sel_clause2.size(); j < e2; j++)
		{
			if ((sel_clause1[i].clause == sel_clause2[j].clause) && (sel_clause1[i].state == sel_clause2[j].state))
				output_CSS.emplace_back(_clause(sel_clause1[i].clause, sel_clause1[i].state));
		}
	}

	//this for loop is important to check if the appended selection is included completely or partially, For instance: we can find that the CSS has included only SCB1_LSB without SCB1_MSB. and this is wrong, as the two bits must be included both or leaved both.
	for (unsigned int n = 0; n < output_CSS.size(); n++) //here we can't use the condition (n<e) as we need to recheck the size of the output_CSS in each iteration.
	{
		index = get_selection_clause_index(output_CSS[n].clause);
		if (NW_stateElements[index].length > output_CSS.size()) //means one comman without the other bit but logically common states means (all the bits for the same controller) share the same state.
			output_CSS.clear(); //this will automatically break the loop as this condition (n < output_CSS.size()) will set to false when the size=0.
	}
}

bool SCT_vertex::has_concurrent_access(vector<_clause>& sel_clause1, vector<_clause>& sel_clause2) //this method is called in two ways: first to check if the SCB/TReg has any NW_TDR in its ASP or not, if yes, we tries to find any SCB in NW_TDR's selection clause with different entry points to be used in unsatisfying the NW_TDR's selectivity and hence excluding it from SCB/TReg ASP.  
{
	for (unsigned int i = 0, e1 = sel_clause1.size(); i < e1; i++)
	{
		for (unsigned int j = 0, e2 = sel_clause2.size(); j < e2; j++)
		{
			if ((sel_clause1[i].clause == sel_clause2[j].clause) && (sel_clause1[i].state != sel_clause2[j].state))
				return false;
		}
	}
	return true; //return true whenever there is no conflict
}

bool SCT_vertex::has_separate_access(vector<_clause>& selections, vector<_clause>& CSS_selections)
{
	//we want to insure that the selections of the controller doesn't completely satisfy the {CSS}. 
	unsigned int selection_index;

	if (selections[0].clause == "TRUE")
		return true; //this is a stopping condition for leaf nodes

	if (is_subset(selections, CSS_selections))
		return false; //it couldn't has a sepearate access, as it have to pass through the TDR and the configured_SCB because of the {CSS} satisfiement.
	
	for (unsigned int i = 0, e1 = selections.size(); i < e1; i++)
	{
		selection_index = get_selection_clause_index(selections[i].clause);
		if (!has_separate_access(NW_stateElements[selection_index].basic_const, CSS_selections))
			return false;
	}

	return true; //means it doesn't completely satisfy the {CSS} by any of its structural and temporal selections.
}

bool SCT_vertex::is_subset(vector<_clause>& superset, vector<_clause>& subset)
{
	unsigned int i, e1, j, e2;
	for (i = 0, e1 = subset.size(); i < e1; i++)
	{
		for (j = 0, e2 = superset.size(); j < e2; j++)
		{
			if ((subset[i].clause == superset[j].clause) && (subset[i].state == superset[j].state))
				break; //break from the for loop of the (superset) once we catch and find the item in the (subset), then check for the next item in the (subset)
		}
		if (j == e2)
			return false; //if we didn't break from the for loop, then it means that we loop over the entire superset and we didn't find the assigned element in the subset. i.e. there exist an item in the subset that doesn *not* exist in the superset
	}

	return true;
}

bool SCT_vertex::has_any_dependenceRelation_with_any_relevantSCB(unsigned int controller_index)
{
	//Here we go through all the passed controller's dependent scan registers, and check if any of them are relevant to the search area
	for (unsigned int i = 0, e = NW_stateElements[controller_index].DSR.size(); i < e; i++)
	{
		if (NW_stateElements[i].relevancy)
			return true;
	}

	return false; //means the controller is not dependent by any relevant SCB
}

void SCT_vertex::set_DSRs_becOF_basicConstraints()
{
	//In this method, we set the DSR group because of basic dependencies and supplemental dependencies
	unsigned int indexOF_dependantSCB;
	for (size_t i = 0, e1 = NW_stateElements.size(); i < e1; i++)
	{
		if (NW_stateElements[i].relevancy && NW_stateElements[i].basic_const[0].clause != "TRUE")
		{
			for (size_t j = 0, e2 = NW_stateElements[i].basic_const.size(); j < e2; j++)
			{
				indexOF_dependantSCB = get_selection_clause_index(NW_stateElements[i].basic_const[j].clause);
				NW_stateElements[indexOF_dependantSCB].DSR.emplace_back(NW_stateElements[i].id);
			}
		}
	}
}

void SCT_vertex::update_DSRs_becOF_supplementalConstraints()
{
	//In this method, we set the DSR group because of basic dependencies and supplemental dependencies
	unsigned int indexOF_dependantSCB;
	for (size_t i = 0, e1 = NW_stateElements.size(); i < e1; i++)
	{
		if (NW_stateElements[i].relevancy && NW_stateElements[i].basic_const[0].clause != "TRUE")
		{
			for (size_t j = 0, e2 = NW_stateElements[i].supp_const.size(); j < e2; j++)
			{
				indexOF_dependantSCB = get_selection_clause_index(NW_stateElements[i].supp_const[j].clause);
				NW_stateElements[indexOF_dependantSCB].DSR.emplace_back(NW_stateElements[i].id);
			}
		}
	}
}
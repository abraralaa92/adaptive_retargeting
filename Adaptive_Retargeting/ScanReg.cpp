#include "ScanReg.h"

//static variables (private variables to the scope of this file)
static size_t Expected_no_constraints, Expected_no_SATvariables;
static vector<unsigned int> index_range; //this variable is used to speed up the search in (NW_SAT_variables) vector, where we only search in a specific range of SAT_variables which occur in the specific time frame. Index of this vector represents the timeFrame number; i.e. search_range[1]: means the search range associated with timeFrame(1)
static unsigned int SATvariable_no;
static unsigned int no_timeFrames = 0; //this variable holds the "current", used number of time frames.
static unsigned int delete_threshold = 0; //this variable is used as a threshold between Benchmarks transformation predicates and Read/Write predicates. Hence, it should be updated to the new threshold with each Read/Write predicates of the new incremented time frame. The threshold is used later in (delete_previousTF_Active_ReadWrite_predicates) method to append on the previous SAT problem without its TF's Reagd/Write predicates.
static void (ScanReg::*selected_retargeting_model)();

static vector<ScanReg> NW_SCBs;		//CSU_Regs(NW_SCBs)
static vector<ScanReg> NW_TDRs;	//Shift_Regs(TDRs) 
static vector<ScanReg*> RSCBs; //pointer to the "relevant" SCBs in the NW_SCBs vector.
static vector<ScanReg*> iRSCBs; //pointer to the "irrelevant" SCBs in the NW_SCBs vector.
static vector<_SAT_predicate> NW_SAT_constraints;
static vector<string> NW_SAT_clauses;
static vector<_SAT_variable> NW_SAT_variables; //used to hold the boolean satisfiable values associated to each SAT_variable, which we get from the SAT solver
static vector<vector<_clause>> SAT_output;   //Two dimensional vector where each time frame has its ASP elements. used to hold the retargeting output vectors, by applying the boolean satisfiable values that we have got by the SAT_solver of each node in the network in each TF to get the Active Scan Path.
static vector<NWElement_statistics>target_registers;

ScanReg::ScanReg()
{}

ScanReg::~ScanReg()
{
	//printf("selection_clause Distructed!!\n");
	vector<_clause>().swap(Selections);
}

void ScanReg::reserve_vectors_memory()
{
	//initialize (SATvariable_no) 
	SATvariable_no = 1;
	unsigned int max_no_timeFrames = 20;
	unsigned int multiplier = 10;

	//Following calculations are just based on finding a relation between numbers and figure out how we could put it in a mathematical equation. These expectations are not exact and are not optimum, so this specific prediction section for (Expected_no_nodes, Expected_no_predicates_forSCT, Expected_no_predicates_forSAT, Expected_no_SAT_clauses, Expected_no_SAT_variables) could be optimized in the future.
	RSCBs.reserve(NW_SCBs.size());		//maximum all network SCBs are relevant to the retargeting problem.
	iRSCBs.reserve(NW_SCBs.size());

	Expected_no_constraints = (NW_SCBs.size() * 2) + (NW_SCBs.size() * max_no_timeFrames * multiplier) * (NW_SCBs.size() * 2);	//(part(1): (NW_SCBs.size() * 2): for initial configuration predicates or initial unit clauses [state and initialized (or) initialized and configured variables]. Second part for state transition predicates: (NW_SCBs.size() * max_no_timeFrames * multiplier): assuming that each node/ScanReg has an average of a "multiplier" predicates per each time frame. last part for target configurations: (NW_SCBs.size() * 2): 2 for [state and initialized (or) initialized and configured].
	Expected_no_SATvariables = Expected_no_constraints / multiplier;

	NW_SAT_constraints.reserve(Expected_no_constraints);
	NW_SAT_variables.reserve(Expected_no_SATvariables); //number of SAT variables almost equal to the number of predicates

	//this vector is used as an index director to the SAT_variables associated to each timeFrame
	index_range.reserve(max_no_timeFrames + 1); //no_timeFrames; since we need to set the search range for each timeFrame. (+1) to account also initial time frame (t0).
	SAT_output.reserve(max_no_timeFrames + 1);   //(+1) to account also initial time frame (t0). Here we only reserve the outer vector capacity, and in the struct (_clause)'s constructor we reserve the internal vector capacity for each time frame.
}

void ScanReg::reset_system()
{
	vector<_SAT_predicate>().swap(NW_SAT_constraints);
	vector<string>().swap(NW_SAT_clauses);
	vector<_SAT_variable>().swap(NW_SAT_variables);
	vector<ScanReg>().swap(NW_SCBs);
	vector<ScanReg>().swap(NW_TDRs);
	vector<unsigned int>().swap(index_range);
	vector<NWElement_statistics>().swap(target_registers);
	
	//Swapping 2D vectors:
	for (unsigned int i = 0, e = SAT_output.size(); i < e; i++)
		vector<_clause>().swap(SAT_output[i]);
	vector<vector<_clause>>().swap(SAT_output);
}

void ScanReg::clear_vectors()
{
	//initialize (SATvariable_no) 
	SATvariable_no = 1;
	no_timeFrames = 0;

	RSCBs.clear();
	iRSCBs.clear();
	NW_SAT_constraints.clear();
	NW_SAT_clauses.clear();
	NW_SAT_variables.clear();
	index_range.clear();
	SAT_output.clear();
}

measurement ScanReg::call_SAT_retargeter()
{
	setup_the_environment(); //load the Selections, reserve the required memory and select the retargeting model

	if (!retarget_all_TDRs)
	{
		target_registers.emplace_back(load_target_configuration()); //from the (pdl) file
		
		setup_the_retargeting_problem();
		print_NWstatistics(true); //means print NW_statistics for this "SPECIFIC" TDR.
	}
	else
	{
		target_registers.reserve(NW_TDRs.size());
		for (size_t i = 0, e = NW_TDRs.size(); i < e; i++)
		{
			target_registers.emplace_back(NW_TDRs[i].id);
			setup_the_retargeting_problem(); //according to the selected target_reg
			clear_vectors(); //reset the system for the next TDR retargeting 
		}
		print_NWstatistics(false); //means print NW_statistics for the whole network for "ALL" Network_TDRS.
	}

	measurement execution_time(get_avg('E'), get_avg('C'), get_avg('A')); //this is the average of all network's TDRs retargeting times. The average calculated in the main() file, is the average of re-applying the retargeting process on the same network and under the same conditions for number of times (setted by the "no_readings" parameter).
	print_vectors_size_capacity_comparison(); ////Finally I need to 'update' (NW_vectors_sizes) with NW SAT vectors statistics
	clear_vectors(); 
	return execution_time;
}

void ScanReg::setup_the_environment()
{
	if (!optimal_solution) //means we want the "First_Solution" which depends "only" on (structural and temporal dependency) of the target_reg_SCT
		selected_retargeting_model = &ScanReg::first_retargeting_model;

	else //optimal_retargeting
		selected_retargeting_model = &ScanReg::optimal_retargeting_model;
	
	load_NW_Selections(); //here we load the selections for all network scan segments (SCBs and TDRs)
	reserve_vectors_memory();
}

void ScanReg::setup_the_retargeting_problem()
{
	if (NW_TDRs[get_literal_index(target_registers.back().reg_id)].Selections[0].clause == "TRUE")//if this is the case, then it means the target_reg is an "always-active" TDR, and it is already part of the ASP, and hence "no" retargeting problem (either first or optimal retargeting) is exist in the first place to be resolved!!
	{
		no_CSUs = 0;
		target_registers.back().solver_returns.emplace_back(0, 0, 0); //execution_time(a), n_conflicts(b), AccessTime(c)
		generate_output_retargeting_vector();
		compute_no_clockCycles(); //re-compute the Accesstime based on the network ASP.
		print_file(SAT_retargeting_vectors, path + "SAT_instance_retargeting_vectors.txt", "a");
	}
	else
		(*this.*selected_retargeting_model)(); //invoke the selected retargeting model, either it was first/optimal.
}

string ScanReg::load_target_configuration()
{
	//set (target_reg) name from "pdl" file
	//"In Future" I need to loop onto "vector<string>target_registers", in order to generate the final report.
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

void ScanReg::first_retargeting_model()
{
	//Here we call (generate_TReg_SCT) and not (build_search_space): to build the search space with the *min_constraints*; where (TReg_SCT) holds only Structural and Temporal dependencies with the TReg (NO LPC). We are only seeking the retargeting with the first solution which maintain the min number of CSUs.
	set_RSCBs(NW_TDRs[get_literal_index(target_registers.back().reg_id)]); //this holds structural and temporal dependencies. 
	
	if (no_CSUs != 0)
	{
		first_retargeting_oneCall_model();
	}
	else
		first_retargeting_incremental_model();
}

void ScanReg::first_retargeting_oneCall_model()
{
	//Here the number of CSUs needed for first_solution is known, and hence we could call/unroll the SAT_Solver for only "one" time, seeking for the retargeting vectors within the min #CSUs.
	no_timeFrames = no_CSUs;

	generate_SAT_instance(); //this would unroll the SAT Solver for only "one" time using the pre-defined number of CSUs.
	convert_constraints_to_CNF();

	if (is_SAT_instance_satisfiable()) //this condition is crucial because the SAT_problem may not have solution at all *using* the assigned number of CSUs
		printf("\nThe Retargeting of (%s) is SATISFIABLE using (%d) CSUs\n", target_registers.back().reg_id.c_str(), no_timeFrames);
}

void ScanReg::first_retargeting_incremental_model()
{
	generate_incremental_SAT_instance(); //here we construct an initial SAT_instance for the (TF=0) where it would be used in the "first unrollment" of the SAT_Solver inside the next (while loop).
	convert_constraints_to_CNF();

	while (!is_SAT_instance_satisfiable())
	{
		no_timeFrames++;
		generate_incremental_SAT_instance(); //here we unroll the SAT Solver for a "number" of times until a solution is found. Iinitially (target_registers.back().no_timeFrames = 0).
		convert_constraints_to_CNF();
	}

	no_CSUs = no_timeFrames;
	printf("\nThe Retargeting of (%s) is SATISFIABLE using (%d) CSUs\n", target_registers.back().reg_id.c_str(), no_CSUs);
}

void ScanReg::load_NW_Selections()
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

		//First line holds NW_SCBs size and second line holds NW_TDRs size.
		getline(data_file, line);
		NW_SCBs.reserve(stoi(line));

		getline(data_file, line);
		NW_TDRs.reserve(stoi(line) + 1); //(+1) in case we need to add ("V.Instrument") through the (UBC) problem.

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
				NW_SCBs.emplace_back(id, length, reset_value, selection_clause); //_clause=NULL because it will be updated after that with a vector of clauses through (split_selection_clause_into_vectorOfClauses) method.initial_configuration represent (initial state and reset state)
			else  //This condition to select all target_registers since they have only select_variables because they are shift_registers, however, other network SCBs are CSU_regs with state and select varaiables which could be updated from one time frame to another with different values until target_reg become part of the ASP.
				NW_TDRs.emplace_back(id, length, reset_value, selection_clause);
		}
	}
}

void ScanReg::set_RSCBs(ScanReg& target_register) //this method is setting only "relevancy" flag for all vertices which belongs to search_space
{
	set_Relevancy_dueTo_StructuralAndSequential_dependencies(target_register);
	if (redundant_arbitrary) //"True" means the examined network has an "arbitrary" structure
	{
		for (size_t i = 0; i < RSCBs.size(); i++) //not i<e as we need to recompte the size of relevant registers each time in case it has been updated with additional relevant SCBs because of irrelevant_TDRs_removal_constraints
			set_Relevancy_dueTo_IrrelevantTDRsRemoval_dependencies(*RSCBs[i]);
		set_Relevancy_dueTo_IrrelevantTDRsRemoval_dependencies(target_register);

		set_iRSCBs();
		set_Relevancy_dueTo_ActiveVisited_dependencies();
	}
	else
		set_iRSCBs();
}

void ScanReg::set_Relevancy_dueTo_StructuralAndSequential_dependencies(ScanReg& scan_register)
{
	unsigned int index;
	for (size_t i = 0, e = scan_register.Selections.size(); i < e; i++)
	{
		index = get_literal_index(scan_register.Selections[i].clause);
		
		if (!findSCB(RSCBs, NW_SCBs[index].id)) //if it has a structural or sequential dependencies with the target configuration and it hasn't been involved before, then include it, otherwise stop the recursion and return back.
		{
			RSCBs.emplace_back(&NW_SCBs[index]);
			if (NW_SCBs[index].Selections[0].clause != "TRUE")
				set_Relevancy_dueTo_StructuralAndSequential_dependencies(NW_SCBs[index]); //apply recursion to set the SCB's relevancy because of temporal dependencies also
		}
	}
}

void ScanReg::set_Relevancy_dueTo_IrrelevantTDRsRemoval_dependencies(ScanReg& RR)
{
	unsigned int i, j, e1, e2, controller_index; //this (unsigned int) in spite of the function's argument is (int); because this is would be a correct_setted value of index and we would not neet (-1) for use.
	vector<_clause> SSS; //SSS: shared selection set
	SSS.reserve(5); //this is a random picked value

	//this is an optimal condition to stop seeking for LCP in case the passed reg was an "always-Active" reg. //(NW_SCBs[i].clause[0].clause != "TRUE"): this condition to exclude always-active SCBs, since those SCBs are part of any active scan path and "no way" to exclude target_registers without passing through those always-active SCBs.
	if (RR.Selections[0].clause == "TRUE")
		return;

	for (i = 0, e1 = NW_TDRs.size(); i < e1; i++)
	{
		if (NW_TDRs[i].Selections[0].clause != "TRUE") //For optimality, we ignore always-active target_registers; because there is no way to deActivate them before passing through the configured_SCBs.ASP.
		{
			get_common_selections(RR.Selections, NW_TDRs[i].Selections, SSS); //SSS is the return from function

			if (!SSS.empty() && has_concurrent_access(RR.Selections, NW_TDRs[i].Selections))  //First condition: To insure the existence of any dependency between the configured SCB and the network TDR and thus we could try later to break this dependency seeking for optimum retargeting cost . Second condition to insure if the TDR is part of the ASP of any SCB in the SCT or not. (has_concurrent_access) means no conflict. 
			{
				for (j = 0, e2 = NW_TDRs[i].Selections.size(); j < e2; j++) //here we loop on TDR's controllers seeking for external or separately accessed one.
				{
					controller_index = get_literal_index(NW_TDRs[i].Selections[j].clause);

					if ((find(SSS.begin(), SSS.end(), NW_SCBs[controller_index].id) == SSS.end()) && (has_separate_access(NW_SCBs[controller_index].Selections, SSS))) //first condition to insure that the selected controller is not one of the CSS's SCBs. While the other to insure that it can be accessed away from the TDR and the CR from different separate accessed path.
					{
						if (!has_any_dependenceRelation_with_any_relevantSCB(controller_index))
						{
							if (!findSCB(RSCBs, NW_SCBs[controller_index].id))
							{
								RSCBs.emplace_back(&NW_SCBs[controller_index]);
								set_Relevancy_dueTo_StructuralAndSequential_dependencies(NW_SCBs[controller_index]);
							}
						}
					}
				}
			}

			SSS.clear();
		}
	}

	vector<_clause>().swap(SSS);
}

void ScanReg::set_Relevancy_dueTo_ActiveVisited_dependencies()
{
	unsigned int num_Relevant_SCBs = RSCBs.size(); //this is the number of relevant registers due to only (structural, sequential and TDRs removal) dependencies, I need to compute it in the beginnig before visited nodes get involved in the relevant regsters set. Since we set visited SCBs relevant to those SCBs only and not the ones relevant to "visited" SCBs.

	//this is to set visited nodes during subsequent configuration paths, including the initial and target configuration paths.
	for (size_t i = 0; i < iRSCBs.size(); i++) //this is a loop on irrelevant SCBs to check if any of them are visited through any of the configuration paths, the size needs to be recomputed each loop since an SCB can be erased from the iRRelvant set and push into the Relevant one.
	{
		if (iRSCBs[i]->Selections[0].clause == "TRUE")
		{
			RSCBs.emplace_back(iRSCBs[i]);
			iRSCBs.erase(iRSCBs.begin() + i);
			i--; //since visited elements will be erased, then the index i should be shifted back
		}
		else //this for subsequent configuration paths
		{
			for (size_t j = 0; j < num_Relevant_SCBs; j++) // (j < num_Relevant_SCBs) and not (j < RSCBs.size()) as I don't want to recompute size each time since this would consider also the new involved set of visited nodes, however, we only seek relevant registers that have either (structural, sequential or TDRs removal) dependencies. Therefore we stop the looping on the primary-Related SCBs only. //this is the number of relevant registers due to only (structural, sequential and TDRs removal) dependencies, I need to compute it in the beginnig before visited nodes get involved in the relevant regsters set. Since we set visited SCBs relevant to those SCBs only and not the ones relevant to "visited" SCBs.
			{
				if ((RSCBs[j]->Selections[0].clause != "TRUE") && (has_concurrent_access(iRSCBs[i]->Selections, RSCBs[j]->Selections))) //iterator (i) is used with iRSCBs vector, while iterator (j) is used with RSCBs vector. Concurrent Activation with "Always-Active" irrelevant-SCBs have been already considered through the first if condition that's why we ignore it here.
				{
					RSCBs.emplace_back(iRSCBs[i]);
					iRSCBs.erase(iRSCBs.begin() + i);
					i--; //since visited elements will be erased, then the index i should be shifted back
					break;
				}
			}
		}
	}
}

void ScanReg::set_iRSCBs()
{
	//collect the set of iRRelevant SCBs
	for (size_t i = 0, e = NW_SCBs.size(); i < e; i++) //not i<e as we need to recompte the size of relevant registers each time in case it has been updated with additional relevant SCBs because of irrelevant_TDRs_removal_constraints
	{
		if (!findSCB(RSCBs, NW_SCBs[i].id))
			iRSCBs.emplace_back(&NW_SCBs[i]);
	}
}

void ScanReg::optimal_retargeting_model()
{
	unsigned int index_of_optimal_cost;		//which reflect the min number of Cycles needed for the optimal retargeting.
	target_registers.back().solver_returns.reserve((no_CSUs + 1) * 10);        //(*10): this reservation is only a rnd value we pick without any scientific reason. so we are assuming that each time frame has an average of "10" different possible solutions. We are considering each TF; because when we enter that (#CSUs = 5) to the SAT solver, then it will look for solutions in (TF=0, TF=1, TF=2, TF=3, TF=4, TF=5) that's why we need to take all previous TFs into considerations while reserving the vectors capacity.
	target_registers.back().solver_returns.emplace_back(); //adjust a place in the (solver_returns) vector to be "directly" used in setting SAT_solver output values.
	
	auto start = std::chrono::steady_clock::now();
	set_RSCBs(NW_TDRs[get_literal_index(target_registers.back().reg_id)]);

	while (no_timeFrames <= no_CSUs)
	{
		generate_incremental_SAT_instance(); //here we input the (UB_CSUs + SCT[SD+TD+LPC]).
		convert_constraints_to_CNF();
		//convert_constraints_to_CNF_withIDs();

		//In optimal retargeting we apply multiple calls to the SAT_solver using (is_SAT_instance_satisfiable()) to search for all possible solutions in the search space using the assigned no_timeFrames until the whole space is examined and traversed and no other solutions could possibly exist.
		while (is_SAT_instance_satisfiable()) //This condition means the SAT_solver still finds other solutions, so we need to loop on all of them until all the possible solutions using this number of time frames are realized.
			update_SAT_instance(path + "SAT_instance.txt");	//update SAT_problem: append the "NEGATION" of the found solution to the SAT_problem to look for other solutions, until the solver returns (UNSATISFIABLE) or (empty) satisfiable_string inidicating that there is no other "different" solutions with this upper_bound number of CSUs.

		no_timeFrames++;
	}

	target_registers.back().solver_returns.erase(target_registers.back().solver_returns.end() - 1); //Remove "UNSAT" solutions, as it returns ""
	index_of_optimal_cost = find_optimal_solution(); // like min = x[0]; here we only set min value to the first index in the vector and compare others to it.
	auto elapsed = std::chrono::steady_clock::now() - start;

	printf("\n***Min number of clock cycles for the retargeting of (%s), using (%d) CSUs = %f***\n", target_registers.back().reg_id.c_str(), target_registers.back().solver_returns[index_of_optimal_cost].no_CSUs, target_registers.back().solver_returns[index_of_optimal_cost].AccessTime);
	printf("Total ececution time = (%f) sec\n", get_total('E')); //std::chrono::duration<double>(elapsed).count()
	printf("Total number of conflicts = (%f) sec\n", get_total('C')); //std::chrono::duration<double>(elapsed).count()
}

void ScanReg::update_SAT_instance(const string& file_name)
{
	//This method is used to append only the "negation" of the satisfiable_string to the SAT_problem but we need to (reWrite) the "SAT_instance.txt" file because the number of SAT clauses has been updated and we need to reflect that in the first line of the CNF file be reWriting it, where there is no any other possibility to do this except bt the reWriting. https://stackoverflow.com/questions/9505085/replace-a-line-in-text-file
	//First update the number of SAT clauses to include the (negated_staisfiable_str) clause also, using the updated size value (NW_SAT_clauses.size()).
	NW_SAT_clauses[0] = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_clauses.size());

	//Second append the (negated_staisfiable_str) to the original SAT problem.
	NW_SAT_clauses.emplace_back(get_negated_string(target_registers.back().solver_returns.back().satisfiable_string));

	//Third reWrite the SAT problem taking into consideration all found solution to let the SAT solver seek for other different solutions.
	print_file(SAT_clauses, path + "SAT_instance.txt", "w");

	//Fourth a new vector for the next retargeting solution
	target_registers.back().solver_returns.emplace_back();

	//Finally reset the (SAT_output) to be used in the next retargeting.
	SAT_output.clear();
}

unsigned int ScanReg::find_optimal_solution()
{
	unsigned int index_of_optimal_cost = 0;
	for (size_t i = 0, e = target_registers.back().solver_returns.size(); i < e; i++)
	{
		if (target_registers.back().solver_returns[i].AccessTime < target_registers.back().solver_returns[index_of_optimal_cost].AccessTime)
			index_of_optimal_cost = i;
	}
	return index_of_optimal_cost;
}

void ScanReg::generate_SAT_instance()
{
	starting_configuration_constraints();

	for (unsigned int t = 0; t < no_CSUs; t++)  //notice that we used here (no_CSUs) and not (no_timeFrames) as usual, as we use (no_timeFrames) if we are applying the incremental SAT model, until the (no_CSUs) reaches the (no_timeFrames). 
	{
		//Here we set the SAT_variables' search range for time frame "(t+1)"
		index_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with timeFrame/index (t+1) not (t).
		subsequent_transitioning_constraints(t, t + 1);
	}

	target_configuration_constraints();
	target_registers.back().n_SAT_variables = NW_SAT_variables.size();//set the number of (SAT_variables) to the "first_chosen" target_reg.
}

void ScanReg::generate_incremental_SAT_instance()
{
	if (no_timeFrames == 0) //if this is the "initial" time frame:
	{
		starting_configuration_constraints();
		target_configuration_constraints();

		target_registers.back().n_SAT_variables = NW_SAT_variables.size();//set the number of (SAT_variables), "initially".
	}
	else //here we use the (incremental_SAT) in successor time frames. 
	{
		//First we remove the predicates associated with the previous time frame
		delete_previousTF_target_configuration_constraints();

		//add the predicates associated with the "just added" time frame.
		index_range.emplace_back(NW_SAT_variables.size()); //this is the search range associated with timeFrame/index (t+1) not (t).
		subsequent_transitioning_constraints(no_timeFrames - 1, no_timeFrames);

		target_configuration_constraints(); //regenerate it for using the "incremental" number of time frames.
		target_registers.back().n_SAT_variables = NW_SAT_variables.size(); //"update" the number of (SAT_variables) to the "new" target_reg.
	}
}

void ScanReg::delete_previousTF_target_configuration_constraints()
{
	for (unsigned int i = NW_SAT_constraints.size(), s = delete_threshold; i > s; i--)
		NW_SAT_constraints.erase(NW_SAT_constraints.end() - 1);
}

void ScanReg::starting_configuration_constraints()
{
	index_range.emplace_back(NW_SAT_variables.size());  //this is the NW_SAT_variables's search_range for time frame(t0). it means the search_range of SAT_variables associated with timeFrame(0) starts from index[0], where initially: (NW_SAT_variables.size()=0).

	for (size_t i = 0, e = RSCBs.size(); i < e; i++)
	{
		//this is for (state) variable: type(1), we only add the SCB.state to NW_SAT_variables, without NW_SAT_predicates.
		NW_SAT_variables.emplace_back(RSCBs[i]->id, 0, SATvariable_no++);
		NW_SAT_constraints.emplace_back(RSCBs[i]->id, 0, initial_configuration); //in retargeting we need to go from "certain" initial configuration, to a "certain" target configuration. It can't be vague,unkwon or uninitialized like in (UBC) SAT problems. 
	}
}

void ScanReg::subsequent_transitioning_constraints(unsigned int fromTF, unsigned int toTF)
{
	//Notes: this is the only method which should set the "state" variable, because the RHS in the implication relation generated from the SCT, holds the "state" values (or the address inputs of the muxes) which we need to *satisfy*
	//includes both state elements transition and active tranition in a combined implication realtion.
	//in this method I could update only the states of (SIBs, SCBs) if it is Active. However, for state Elements (other than the target reg) its states should be the same (Equilvalent relation)
	//for SIB NWs: we set (Non interesred variables) to reset state, while all other SCT's variables are activated based on the selection clauses states. However, for MUX NWs: (all variables) are activated based on the selection clauses states, this could be handeled by checking first the value of (belongsTo_SCT) attribute, where it is always equal to true for MUX NWs.
	
	for (size_t i = 0, e1 = RSCBs.size(); i < e1; i++)
	{
		NW_SAT_variables.emplace_back(RSCBs[i]->id, toTF, SATvariable_no++);

		if (RSCBs[i]->Selections[0].clause != "TRUE")
		{
			//Each literal from the "RHS" should be inserted in a seperate predicate; because SAT literals in the "RHS" are (ANDed) together so, we can seperate them into multiple (ANDed predicates).
			//RHS literals are XORed, so for each (NW_clauses[i].clause[j]) we have to insert two predicate. [A XOR B --> C] is the same as [!A OR B OR C, A OR !B OR C]

			//only Selections are included, while ITRC are included only in relative registers without the access modeling constraints, where adding them force reaching the target configurations through the longest configuration path as in the Upper-Bound problem.
			for (size_t j = 0, e2 = RSCBs[i]->Selections.size(); j < e2; j++)
			{
				NW_SAT_constraints.emplace_back(3); // needs (3) for: LHS(fromTF) XOR LHS(toTF)--> RHS(fromTF)
				NW_SAT_constraints.back().SAT_literals.emplace_back(RSCBs[i]->id, fromTF, 0);	//state=0 since we implement (!A OR B OR C)
				NW_SAT_constraints.back().SAT_literals.emplace_back(RSCBs[i]->id, toTF, 1);
				NW_SAT_constraints.back().SAT_literals.emplace_back(RSCBs[i]->Selections[j].clause, fromTF, RSCBs[i]->Selections[j].state);

				NW_SAT_constraints.emplace_back(3);
				NW_SAT_constraints.back().SAT_literals.emplace_back(RSCBs[i]->id, fromTF, 1);	//state=1 since we implement (A OR !B OR C)
				NW_SAT_constraints.back().SAT_literals.emplace_back(RSCBs[i]->id, toTF, 0);
				NW_SAT_constraints.back().SAT_literals.emplace_back(RSCBs[i]->Selections[j].clause, fromTF, RSCBs[i]->Selections[j].state);
			}
		}
		else
		{
			//state = (1) and (0) to insert (state(SR1, t1) OR !state(SR1, t1)) indicating this is an "Active" node
			NW_SAT_constraints.emplace_back(2);

			//here both are inserted in the same statement because they are (ORed) not (ANDed): {state(SR1, t1) OR !state(SR1, t1)}, so it is only *one* statement with *two* literals
			NW_SAT_constraints.back().SAT_literals.emplace_back(RSCBs[i]->id, toTF, 1);
			NW_SAT_constraints.back().SAT_literals.emplace_back(RSCBs[i]->id, toTF, 0);
		}
	}
}

void ScanReg::target_configuration_constraints()
{
	unsigned int target_reg_index = get_literal_index(target_registers.back().reg_id);

	delete_threshold = NW_SAT_constraints.size(); //here we update the Read/Write threshold associated with the current time frame. So that, if no solution was found we could unroll back all the SAT_preducates associated with the previous time frame. 

	if (NW_TDRs[target_reg_index].Selections[0].clause != "TRUE") //if this is the case, then the target_reg is already part of the ASP and the SAT problem is originally  SATISFIABLE.
	{
		//only for Selections, while ITRC are included through relevnt registers.
		for (size_t i = 0, e = NW_TDRs[target_reg_index].Selections.size(); i < e; i++)  //looping on the literals of the selection clause of the target_reg to make sure they all satisfied for the purpose of the Read/ Write Requests.
			NW_SAT_constraints.emplace_back(NW_TDRs[target_reg_index].Selections[i].clause, no_timeFrames, NW_TDRs[target_reg_index].Selections[i].state); //"state" associated to each tareget_reg's selection clause, for EX: Active(I2)= SCB1 ^ !SCB3
	}
}

void ScanReg::convert_constraints_to_CNF()
{
	string CNF_clause, negation;

	//First we need to clear the old SAT problem in case of any and we replace it with the new one. (new SAT instance could represents the "same" retargeting/UBC problem but using "more" number of time frames, or it could represents "different" retargeting/UBC problem for another NW_TDR in the same network. That's why we need each time to clear/reset the old instance first.
	if (NW_SAT_clauses.size() == 0)
		NW_SAT_clauses.reserve(NW_SAT_constraints.size() + 1 + target_registers.back().solver_returns.capacity()); //SAT_clauses vector has the same size as SAT_predicates vector; where the only difference between the two vectors is that in SAT_clauses vector we replace each SAT_literal with its corresponding SAT_no, also (+1) to account for the "p cnf " line, (+possibleRetargetings.capacity()) in case the user request the optimal solution, where we have to append to the CNF clauses all the found/possible solutions
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
				CNF_clause += negation + to_string(get_SATvariable_no(NW_SAT_constraints[i].SAT_literals[j].id, NW_SAT_constraints[i].SAT_literals[j].timeFrame)) + " ";
			}
			if (j == e2 - 1)
				CNF_clause += "0";
		}

		NW_SAT_clauses.emplace_back(CNF_clause);
	}
	target_registers.back().n_SAT_clauses = NW_SAT_clauses.size() - 1; //(-1) to exclude the first line (p cnf ..)

	//This is a *very important* step for (the optimal *Retargeting* problems): where we need to exclude also all previously obtained solutions from the search space as they were already considered before in our possible retargeting solutions; and this is by incuding their negated_satisfiable_string in our SAT_problem.
	if (optimal_solution) 
	{
		for (unsigned int i = 0, e = target_registers.back().solver_returns.size(); i < e; i++)
		{
			if(target_registers.back().solver_returns[i].satisfiable_string != "")
				NW_SAT_clauses.emplace_back(get_negated_string(target_registers.back().solver_returns[i].satisfiable_string));
		}

		//Next update the number of SAT clauses to include the previously examined retargeting solutions also, using the updated size value (NW_SAT_clauses.size()).
		if (NW_SAT_constraints.size() < NW_SAT_clauses.size() - 1) //means a satisfying_assignment solutions have beed added and we need to re-update the no_SAT_clauses. (NW_SAT_clauses.size() - 1): (-1) to unconsider the (p cnf ..) clause.
			NW_SAT_clauses[0] = "p cnf " + to_string(SATvariable_no - 1) + " " + to_string(NW_SAT_clauses.size() - 1);
	}

	print_file(SAT_clauses, path + "SAT_instance.txt", "w");
}

void ScanReg::convert_constraints_to_CNF_withIDs()
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
				CNF_clause += "state(" + NW_SAT_constraints[i].SAT_literals[j].id + ", " + to_string(NW_SAT_constraints[i].SAT_literals[j].timeFrame) + ", " + to_string(get_SATvariable_no(NW_SAT_constraints[i].SAT_literals[j].id, NW_SAT_constraints[i].SAT_literals[j].timeFrame)) + ") ";
			}
			if (j == e2 - 1)
				CNF_clause += "0";
		}

		NW_SAT_clauses.emplace_back(CNF_clause);
	}

	// here we append "a" to the original SAT_clauses, the same SAT_clauses but writen in meaningful or understandable way!!
	print_file(SAT_clauses, path + "SAT_instance_withIDs.txt", "w");
}

bool ScanReg::is_SAT_instance_satisfiable()
{
	//1- run the SAT_solver on the updated (SAT_problem), updated with other found solutions in case of optimal_retargeting active choice.
	run_SAT_solver_withNoPrint(path + "SAT_instance.txt", target_registers.back().solver_returns.back());
	
	if (target_registers.back().solver_returns.back().satisfiable_string.length() != 0) //means the problem is "SATISFIABLE"
	{
		if (target_registers.back().solver_returns.back().n_conflicts > 0)
			printf("\nSAT solver has conflicts = %f, while retargeting (%s)\n", target_registers.back().solver_returns.back().n_conflicts, target_registers.back().reg_id.c_str());

		//2- assign the currently used number of time frames to the SAT solutionn we just got.
		target_registers.back().solver_returns.back().no_CSUs = no_timeFrames;

		//3- set (SAT_assignment) values returned by the SAT solver for each SAT vertex in the network, this operation should be applied on each time frame.
		map_SATAssignmentSolution_to_SATvariables();

		//4- Generate Active Scan Path associated with each time frame.
		generate_output_retargeting_vector();

		//5- Compute the number of clock cycles for the Retargeting_Solution associated with the current satisfiable_string;
		compute_no_clockCycles();

		//6- Generate NW "retargeting" output vectors which should be entered to the TAP controller to read/write the value in the target_reg.
		print_file(SAT_retargeting_vectors, path + "SAT_instance_retargeting_vectors.txt", "a");

		return true;
	}
	else
		return false;
}

void ScanReg::compute_no_clockCycles()
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

	target_registers.back().solver_returns.back().AccessTime = no_clkCycles;
}

void ScanReg::generate_output_retargeting_vector()
{
	//To find the scan-in data for the primary scan input of a network in the i-th CSU operation, the network’s graph is traversed along the active scan path of frame i − 1. The content of visited scan segments is acquired from the i-th time frame of the satisfying assignment.
	//so ASP can be concluded from the sel() value of time frame (TF).
	//while constent of ASP can be infered from the state() value of time frame (TF+1).

	unsigned int TF = 0;
	unsigned int sat_assignment;
	unsigned int NW_size = NW_SCBs.size() + NW_TDRs.size();

	//reserve space for the "initial" Time Frame
	SAT_output.emplace_back(); //this constructor is used with any two dimentional vector, where this emplace_back() is used with the outer vector to initialize and reserve the internal vector capacity.
	SAT_output.back().reserve(NW_size); //this is the max that all NW state elements and NW shift registers are part of the ASP.

	if (no_timeFrames > 0)
	{
		for (size_t index = 0, e = NW_SAT_variables.size(); index < e; index++) //NW_SAT_variables represent the variables in the SCT in each TF, so, we need to include "other" NW_SCBs and "all" target_registers which are not in the SCT, however they could be part of the ASP.
		{
			if (NW_SAT_variables[index].timeFrame == TF)
			{
				if (is_Active_SCB(NW_SAT_variables[index].id, NW_SAT_variables[index].timeFrame))	//construct Active Scan Path (ASP) each time frame, by concatenating all active state elements through the "same" time frame. So we check if this SAT_varaible is Active at this TF or not. //the returning index belonging to (NW_SCBs) because we are looping on (NW_SAT_variables) which constructed from (NW_SCBs).
				{
					if (TF < no_timeFrames)
					{
						sat_assignment = get_SATvariable_assignment(NW_SAT_variables[index].id, TF + 1); //(TF+1) b/c I want the content/state of the scan segment from the next TF of the satisfying assignmnet after identifying that it is Active. 
						SAT_output.back().emplace_back(NW_SAT_variables[index].id, sat_assignment);
					}
					else //if(TF == no_timeFrames). for the last TF, we need to consider only the (select) variable, which would be used in generating the last ASP, and hence to be considered while computing the number of cycles associated with each retargeting solution.
						SAT_output.back().emplace_back(NW_SAT_variables[index].id, 0); // 0 refers to the reset state.
				}
			}
			else
			{
				//Before moving to the next time frame we need to generate also the "select" state of other NW_SCBs which were not part of the SCT and also all network "TDRs/Shift_Registers"; because they could be also part of the ASP.
				update_ASP_with_scanRegisters_outside_theSearchSpace(TF);

				//Now we could move to the next TF:
				TF++;
				index--; //to "Recheck" on that SAT_variable (NW_SAT_variables[i].timeFrame) after updating the time frame slot associated with the next CSU output vector.

				//reserve space for the the "next" Time Frame
				SAT_output.emplace_back();
				SAT_output.back().reserve(NW_size);
			}
		}
		update_ASP_with_scanRegisters_outside_theSearchSpace(TF); //this is for the last TF.
	}
	else //in case (TF==0), generate the output from the "initial_configuration" input, where the (target_reg) is *already* Active and accessable with no need for any retargetig vectors to put it on the ASP.
	{
		bool active;
		for (size_t i = 0, e1 = NW_SCBs.size(); i < e1; i++) //for NW_SCBs not in the SCT
		{
			active = true;
			if (NW_SCBs[i].Selections[0].clause != "TRUE")
			{
				for (size_t j = 0, e2 = NW_SCBs[i].Selections.size(); j < e2; j++) //for NW_SCBs not in the SCT
				{
					if (NW_SCBs[i].Selections[j].state != initial_configuration)
					{
						active = false;
						break;
					}
				}
			}
			if (active)
				SAT_output.back().emplace_back(NW_SCBs[i].id, initial_configuration);
		}
		for (size_t i = 0, e1 = NW_TDRs.size(); i < e1; i++) //for NW_SCBs not in the SCT
		{
			active = true;
			if (NW_TDRs[i].Selections[0].clause != "TRUE")
			{
				for (size_t j = 0, e2 = NW_TDRs[i].Selections.size(); j < e2; j++) //for NW_SCBs not in the SCT
				{
					if (NW_TDRs[i].Selections[j].state != initial_configuration)
					{
						active = false;
						break;
					}
				}
			}
			if (active)
				SAT_output.back().emplace_back(NW_TDRs[i].id, -1); //(-1) means (UNKOWN) state, where the shift_register's "state" value is assumed to be unkown we only predict its "select" state if it is Active or not through each TF.
		}
	}
}

void ScanReg::print_file(_SAT_Type option, const string& file_name, const string& file_opening_option)
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
			output_text = "The Retaregeting output vectors for (" + target_registers.back().reg_id + ") using (" + to_string(no_timeFrames) + " CSUs) is: \n";
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

			output_text += "Number of Clock Cycles = " + to_string(target_registers.back().solver_returns.back().AccessTime) + "\n"; //(no_CSUs == 0) if the TDR was already included into the ASP
			output_text += "/////////////////////////////////////////////////////////////////////////////\n";
			break;
		}
		}
		fprintf(file, "%s", output_text.c_str());
		fclose(file);
	}
	else printf("%s \n", "Unable to open file");
}

void ScanReg::print_vectors_size_capacity_comparison()
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

void ScanReg::print_NWstatistics(bool target_statistics, unsigned int index)
{
	//statistics for specific "target_reg"
	if ((target_statistics) && (target_registers[index].solver_returns.size() > 0)) //(target_registers[index].solver_returns.size() > 0) check if there exist a retargeting solution or not!!
	{
		printf("\n//////////////////////////////////////////////////////////////////");
		printf("\n*******For %s: *******\n", target_registers[index].reg_id.c_str());
		printf("\nFor SAT_problem size : #variables = %lu, #clauses = %lu", target_registers[index].n_SAT_variables, target_registers[index].n_SAT_clauses);
		printf("\nAverage number of Conflicts = %f", get_avg('C'));
		printf("\nAverage execution time = %f s", get_avg('E'));

		printf("\n\n//////////////////////////////////////////////////////////////////\n");
	}

	//statistics for the "whole" NW	
	else if (target_registers[index].solver_returns.size() > 0)
	{
		printf("\n//////////////////////////////////////////////////////////////////");

		printf("\nNumber of TDR's = %d", target_registers.size());
		printf("\nFor SAT_problem size : \n\t#vars_Avg/#clauses_Avg = %f/%f, #vars_Max/#clauses_Max = %f/%f", get_avg('V'), get_avg('L'), get_max('V'), get_max('L'));
		printf("\nFor Conflicts NW parameter:\n\tAvg= %f, Max= %f", get_avg('C'), get_max('C'));
		printf("\nFor Access time(CC) NW parameter:\n\tAvg= %f, Max= %f", get_avg('A'), get_max('A'));
		printf("\nFor Incremental SAT solving(sec) NW parameter:\n\tAvg= %f, Max= %f", get_avg('E'), get_max('E'));

		printf("\n//////////////////////////////////////////////////////////////////\n");
	}
}

unsigned int ScanReg::get_length(const string& id)
{
	for (size_t i = 0, e = NW_TDRs.size(); i < e; i++)
	{
		if (NW_TDRs[i].id == id)
			return NW_TDRs[i].length;
	}
}

string ScanReg::get_negated_string(const string& input)
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

unsigned int ScanReg::get_literal_index(const string& node_id)
{
	if (is_SCB(node_id))
	{
		for (unsigned int index = 0, e = NW_SCBs.size(); index < e; index++)
		{
			if (NW_SCBs[index].id == node_id)
				return index;
		}
	}
	else //in case we look for the selection clause of a NW_TDR.
	{
		for (unsigned int index = 0, e = NW_TDRs.size(); index < e; index++)
		{
			if (NW_TDRs[index].id == node_id)
				return index;
		}
	}
}

unsigned int ScanReg::get_SATvariable_no(const string& id, unsigned int timeFrame)
{
	//For "SCT_to_SAT" implementation, Key=(id, timeFrame)
	//To speed up searching in (NW_SAT_variables) we use 'search_range' variable to search on SATvariable_no within specific/limited range and not looping on the "whole" range of NW_SAT_variables.
	unsigned int start, stop;
	start = index_range[timeFrame];
	stop = (timeFrame < no_timeFrames) ? index_range[timeFrame + 1] : NW_SAT_variables.size(); //(<) condition is more generic than (!=) condition, where (!<) will include (== and >) in one common side.

	for (unsigned int index = start; index < stop; index++)
	{
		if (NW_SAT_variables[index].id == id)
			return NW_SAT_variables[index].SAT_no;
	}

	printf("SAT_variable doesn't exist !!\n");
	exit(0); //if SAT_variable doesn't exist
}

void ScanReg::set_SATvariable_assignment(unsigned int SAT_no, bool SAT_value)
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

unsigned int ScanReg::get_SATvariable_assignment(const string& id, unsigned int timeFrame)
{
	//To speed up searching in (NW_SAT_variables) we use 'search_range' variable to search on SATvariable_no within specific/limited range and not looping on the "whole" range of NW_SAT_variables.
	unsigned int start, stop;
	start = index_range[timeFrame];
	stop = (timeFrame < no_timeFrames) ? index_range[timeFrame + 1] : NW_SAT_variables.size();

	for (unsigned int index = start; index < stop; index++)
	{
		if (NW_SAT_variables[index].id == id)
			return NW_SAT_variables[index].SAT_assignment;
	}

	printf("SAT_variable doesn't exist !!\n");
	exit(0); //"Means it doesn't exist; so, I should throw here an error also.
}

void ScanReg::map_SATAssignmentSolution_to_SATvariables() //extract SAT_assignment values from the "SATISFIABLE" string
{
	istringstream SAT_assignment(target_registers.back().solver_returns.back().satisfiable_string);
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

bool ScanReg::is_Active_SCB(const string& reg_id, unsigned int TF) //this method is used with relevant and irrelevant SCBs
{
	//This section is used to generate the select state for each element in the network using its selection clause. By checking if element's selection clause is satisfied through the passed (TF) and hence the element is Active or not.
	unsigned int SATvariable_assignment = 0;
	unsigned int reg_index = get_literal_index(reg_id); //this one returns indicies relevant to the (NW_SCBs) vector and not (RSCBs)
	
	if (NW_SCBs[reg_index].Selections[0].clause != "TRUE")
	{
		for (size_t i = 0, e1 = NW_SCBs[reg_index].Selections.size(); i < e1; i++)
		{
			if (findSCB(RSCBs, NW_SCBs[reg_index].Selections[i].clause))
				SATvariable_assignment = get_SATvariable_assignment(NW_SCBs[reg_index].Selections[i].clause, TF);
			else
				SATvariable_assignment = initial_configuration; //where in SCT model, we set any SCB outside the SCT to the "reset_state"

			if (NW_SCBs[reg_index].Selections[i].state != SATvariable_assignment) //We need to check if the reg's selection clauses are satisfied within the "same" state element's time frame. We need to compare the "satisfying-value" of each SCB in the selection_clause with the SAT_assginment value for that "state" variable in the corresponding time frame, since we compare the satisfying and SAT_assignment values of the (state) variables; we use the value of (1) <-> (state-variable).
				return false;
		}
	}
	
	return true; //if "all" the literals/children in the selection clause are satisfiable through the same (TF), then the node itself is Active.
}

bool ScanReg::is_Active_TDR(unsigned int selection_clause_index, unsigned int TF)
{
	//This section is used to generate the select state for each element in the network using its selection clause. By checking if element's selection clause is satisfied through the passed (TF) and hence the element is Active or not.
	unsigned int SATvariable_assignment = 0;
	
	if (NW_TDRs[selection_clause_index].Selections[0].clause != "TRUE")
	{
		for (size_t i = 0, e1 = NW_TDRs[selection_clause_index].Selections.size(); i < e1; i++)
		{
			if (findSCB(RSCBs, NW_TDRs[selection_clause_index].Selections[i].clause))
				SATvariable_assignment = get_SATvariable_assignment(NW_TDRs[selection_clause_index].Selections[i].clause, TF);
			else
				SATvariable_assignment = initial_configuration; //where in SCT model, we set any SCB outside the SCT to the "reset_state"
				
			if (NW_TDRs[selection_clause_index].Selections[i].state != SATvariable_assignment) //We need to check if the reg's selection clauses are satisfied within the "same" state element's time frame. We need to compare the "satisfying-value" of each SCB in the selection_clause with the SAT_assginment value for that "state" variable in the corresponding time frame, since we compare the satisfying and SAT_assignment values of the (state) variables; we use the value of (1) <-> (state-variable).
				return false;
		}
	}

	return true; //if "all" the literals/children in the selection clause are satisfiable through the same (TF), then the node itself is Active.
}

bool ScanReg::is_SCB(const string& id)
{
	if ((id.find("SR") != std::string::npos) || (id.find("SCB") != std::string::npos))
		return true;

	return false;
}

void ScanReg::update_ASP_with_scanRegisters_outside_theSearchSpace(unsigned int TF)
{
	for (size_t index = 0, e = iRSCBs.size(); index < e; index++) //for NW_SCBs which are not in the SCT
	{
		if (is_Active_SCB(iRSCBs[index]->id, TF)) //seek for "irrelevant" and "active" SCBs.
			SAT_output.back().emplace_back(iRSCBs[index]->id, initial_configuration);
	}
	for (size_t index = 0, e = NW_TDRs.size(); index < e; index++) //for target_registers
	{
		if (is_Active_TDR(index, TF))  //check if any of them are Active through the selected TF or not.
			SAT_output.back().emplace_back(NW_TDRs[index].id, -1); //(-1) means (UNKOWN) state, where the shift_register's "state" value is assumed to be unkown we only predict its "select" state if it is Active or not through each TF.
	}
}

double ScanReg::get_avg(char x) //A->access time, C->no of Conflicts, E->execution time
{
	double sum_avg = 0;
	double sum_TDR = 0;

	switch (x) {
	case 'A':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of target_registers that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = target_registers.size(); i < e1; i++)
		{
			if ((e2 = target_registers[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += target_registers[i].solver_returns[j].AccessTime;

				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0; //in case the assigned number of CSUs is not sufficient for the retargetting of any NW_TDR, at then (n_retargeted_TDRs=0)!!
	}
	case 'C':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of target_registers that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = target_registers.size(); i < e1; i++)
		{
			if ((e2 = target_registers[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += target_registers[i].solver_returns[j].n_conflicts;

				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0;
	}
	case 'E':
	{
		unsigned int i, j, e1, e2, n_retargeted_TDRs = 0;	//n_retargeted_TDRs: represent the number of target_registers that could be retargetted using the assigned number of CSUs
		for (i = 0, e1 = target_registers.size(); i < e1; i++)
		{
			if ((e2 = target_registers[i].solver_returns.size()) > 0)
			{
				n_retargeted_TDRs++;
				for (j = 0; j < e2; j++)
					sum_avg += target_registers[i].solver_returns[j].execution_time;

				sum_avg /= e2; //took the avg per TDR w.r.t. the different possible retargeting solutions.
				sum_TDR += sum_avg;
				sum_avg = 0; //to be used in the next iteration
			}
		}
		return (n_retargeted_TDRs != 0) ? (sum_TDR / n_retargeted_TDRs) : 0;
	}
	case 'V':
	{
		unsigned int i, e;
		for (i = 0, e = target_registers.size(); i < e; i++)
		{
			sum_TDR += target_registers[i].n_SAT_variables;
		}
		return (sum_TDR / e); //e can't be zero; it mus be at least one target_reg!!
	}
	case 'L':
	{
		unsigned int i, e;
		for (i = 0, e = target_registers.size(); i < e; i++)
		{
			sum_TDR += target_registers[i].n_SAT_clauses;
		}
		return (sum_TDR / e);
	}
	default: std::printf("Passed parameter isn't valid!!\n"); // no error
		return -1;
	}
}

double ScanReg::get_max(char x)
{
	switch (x) {
	case 'A':
	{
		double max = target_registers[0].solver_returns[0].AccessTime;
		for (size_t i = 0, e1 = target_registers.size(); i < e1; i++)//(i,j) start from (0).
		{
			for (size_t j = 0, e2 = target_registers[i].solver_returns.size(); j < e2; j++)
			{
				if (max < target_registers[i].solver_returns[j].AccessTime)
					max = target_registers[i].solver_returns[j].AccessTime;
			}
		}
		return max;
	}
	case 'C':
	{
		double max = target_registers[0].solver_returns[0].n_conflicts;
		for (size_t i = 0, e1 = target_registers.size(); i < e1; i++)//(i,j) start from (0).
		{
			for (size_t j = 0, e2 = target_registers[i].solver_returns.size(); j < e2; j++)
			{
				if (max < target_registers[i].solver_returns[j].n_conflicts)
					max = target_registers[i].solver_returns[j].n_conflicts;
			}
		}
		return max;
	}
	case 'E':
	{
		double max = target_registers[0].solver_returns[0].execution_time;
		for (size_t i = 0, e1 = target_registers.size(); i < e1; i++) //(i,j) start from (0).
		{
			for (size_t j = 0, e2 = target_registers[i].solver_returns.size(); j < e2; j++)
			{
				if (max < target_registers[i].solver_returns[j].execution_time)
					max = target_registers[i].solver_returns[j].execution_time;
			}
		}
		return max;
	}
	case 'V':
	{
		double max = target_registers[0].n_SAT_variables;
		for (size_t i = 1, e = target_registers.size(); i < e; i++)
		{
			if (max < target_registers[i].n_SAT_variables)
				max = target_registers[i].n_SAT_variables;
		}
		return max;
	}
	case 'L':
	{
		double max = target_registers[0].n_SAT_clauses;
		for (size_t i = 1, e = target_registers.size(); i < e; i++)
		{
			if (max < target_registers[i].n_SAT_clauses)
				max = target_registers[i].n_SAT_clauses;
		}
		return max;
	}
	default: printf("Passed parameter isn't valid!!\n"); // no error
		return -1;
	}
}

double ScanReg::get_total(char x)
{
	double sum_total = 0;
	
	switch (x) {
	case 'A':
	{
		for (size_t i = 0, e = target_registers.back().solver_returns.size(); i < e; i++)
			sum_total += target_registers.back().solver_returns[i].AccessTime;

		return sum_total;
	}
	case 'C':
	{
		for (size_t i = 0, e = target_registers.back().solver_returns.size(); i < e; i++)
			sum_total += target_registers.back().solver_returns[i].n_conflicts;

		return sum_total;
	}
	case 'E':
	{
		for (size_t i = 0, e = target_registers.back().solver_returns.size(); i < e; i++)
			sum_total += target_registers.back().solver_returns[i].execution_time;

		return sum_total;
	}
	case 'V':
		return target_registers.back().n_SAT_variables;

	case 'L':
		return target_registers.back().n_SAT_clauses;
		
	default: std::printf("Passed parameter isn't valid!!\n"); // no error
		return -1;
	}
}

void ScanReg::get_common_selections(vector<_clause>& sel_clause1, vector<_clause>& sel_clause2, vector<_clause>& output_SSS)
{
	//The implementation of this method is not completely accurate and need to be re-visited.
	unsigned int index;
	for (unsigned int i = 0, e1 = sel_clause1.size(); i < e1; i++)
	{
		for (unsigned int j = 0, e2 = sel_clause2.size(); j < e2; j++)
		{
			if ((sel_clause1[i].clause == sel_clause2[j].clause) && (sel_clause1[i].state == sel_clause2[j].state))
				output_SSS.emplace_back(_clause(sel_clause1[i].clause, sel_clause1[i].state));
		}
	}

	//this for loop is important to check if the appended selection is included completely or partially, For instance: we can find that the CSS has included only SCB1_LSB without SCB1_MSB. and this is wrong, as the two bits must be included both or leaved both.
	for (unsigned int n = 0; n < output_SSS.size(); n++) //here we can't use the condition (n<e) as we need to recheck the size of the output_CSS in each iteration.
	{
		index = get_literal_index(output_SSS[n].clause);
		if (NW_SCBs[index].length > output_SSS.size()) //means one comman without the other bit but logically common states means (all the bits for the same controller) share the same state.
			output_SSS.clear(); //this will automatically break the loop as this condition (n < output_CSS.size()) will set to false when the size=0.
	}
}

bool ScanReg::has_concurrent_access(vector<_clause>& sel_clause1, vector<_clause>& sel_clause2) //this method is called in two ways: first to check if the SCB/TReg has any NW_TDR in its ASP or not, if yes, we tries to find any SCB in NW_TDR's selection clause with different entry points to be used in unsatisfying the NW_TDR's selectivity and hence excluding it from SCB/TReg ASP.  
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

bool ScanReg::has_separate_access(vector<_clause>& contrl_selections, vector<_clause>& SSS_selections)
{
	//we want to insure that the selections of the controller doesn't completely satisfy the {SSS}. 
	unsigned int selection_index;

	if (is_subset(contrl_selections, SSS_selections))
		return false; //it couldn't has a sepearate access, as it have to pass through the TDR and the configured_SCB because of the {SSS} satisfiement.

	for (unsigned int i = 0, e1 = contrl_selections.size(); i < e1; i++) //This loop to insure that each of the selections of control.Selections has a sepearte access away from the SSS also. Therefore, we insure that {SSS} are not satisfied by both (structural and sequential/temporal) dependencies of the TDR_controller.
	{
		selection_index = get_literal_index(contrl_selections[i].clause);
		if (NW_SCBs[selection_index].Selections[0].clause != "TRUE") //True: means the activation of the SCB doesn't depend on the SSS. This is a stopping condition for "LEAF" nodes in the "for" loop.
		{
			if (!has_separate_access(NW_SCBs[selection_index].Selections, SSS_selections))
				return false;
		}
	}

	return true; //means it doesn't completely satisfy the {SSS} by any of its structural and temporal selections.
}

bool ScanReg::is_subset(vector<_clause>& superset, vector<_clause>& subset)
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

bool ScanReg::has_any_dependenceRelation_with_any_relevantSCB(unsigned int controller_index)
{
	//Here we go through all the passed controller's dependent scan registers, and check if any of them are relevant to the search area
	for (size_t i = 0, e = RSCBs.size(); i < e; i++)
	{
		if (find(RSCBs[i]->Selections.begin(), RSCBs[i]->Selections.end(), NW_SCBs[controller_index].id) != RSCBs[i]->Selections.end())
			return true;
	}

	return false; //means the controller is not dependent by any relevant SCB
}
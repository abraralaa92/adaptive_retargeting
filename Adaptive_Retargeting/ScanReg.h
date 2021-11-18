#ifndef node
#define node

#ifdef _MSC_VER				
#pragma once
#endif  // _MSC_VER

#include "structs.h"

class ScanReg
{
	string id;
	vector<_clause> Selections; //"_": to differentiate between struct clause and string clause
	unsigned int length;
	unsigned int reset_value;

public:
	//static variables: to be "initialized" only "once" in the scope of (all) class's objects.
	static string path;
	static unsigned int initial_configuration; //Our SAT instance could start from (unknown/uninitialized) network state; this is needed in (UBC) problems where we want to set the max no_CSUs from (any initial configuration) !!
	static bool optimal_solution;   //true for Optimal_Solution, false for First_Solution.
	static bool retarget_all_TDRs;
	static bool redundant_arbitrary; //false for "redundant" and true for "arbitrary".
	static unsigned int no_CSUs; 
	
	ScanReg(); //Initial constructor is used to Re-Build NW_clauses from 'NW_clauses.txt' file and Re-Build the NW_TDRs from 'NW_TDRs.txt' file.
	~ScanReg();

	ScanReg(const string& a, const unsigned int& b, const unsigned int& c, const string& selection_clause)
		: id(a), length(b), reset_value(c)
	{
		split_selection_clause_into_vectorOfClauses(selection_clause, Selections);
	}

	ScanReg(ScanReg& x)
		:id(x.id), Selections(x.Selections), length(x.length), reset_value(x.reset_value)
	{
		printf("selection_clause copied!!\n");
	}

	bool findSCB (const vector<ScanReg*>& relevant_SCBs, string const &reg_id) //will be needed inside the 'find' method, otherwise this error will be generated "binary '==': no operator found which takes a left hand operand of type 'reg' .. "
	{
		for (ScanReg *i : relevant_SCBs)
		{
			if (i->id == reg_id)
				return true;
		}
		return false;
	}

	//methods to reset and clear the environment
	void reserve_vectors_memory(); //Very Important method used to minimze the number of copied objects and to adjust the capacity of used vectors for better performance
	void reset_system();
	void clear_vectors();

	//methods to setup the environment
	measurement call_SAT_retargeter(); //I need to return output as copy (not return by reference) since we are going to reset all NW_vectors for successor TDR's retargeting, so I need to keep one copy safe in main!!
	void setup_the_environment();
	void setup_the_retargeting_problem();
	void load_NW_Selections();	//used to set NW_stateElements and NW_selectElements
	string load_target_configuration();  //used to set (target_reg) name 
	
	//methods to set relevant SCBs and relevant configuration paths:
	void set_RSCBs(ScanReg& target_register);
	void set_Relevancy_dueTo_StructuralAndSequential_dependencies(ScanReg& scan_register);
	void set_Relevancy_dueTo_IrrelevantTDRsRemoval_dependencies(ScanReg& relevant_register); //relevant_register: RR
	void set_Relevancy_dueTo_ActiveVisited_dependencies();
	void set_iRSCBs();
	void get_common_selections(vector<_clause>& sel_clause1, vector<_clause>& sel_clause2, vector<_clause>& output_CSS);
	bool has_concurrent_access(vector<_clause>& sel_clause1, vector<_clause>& sel_clause2);
	bool has_separate_access(vector<_clause>& contrl_selections, vector<_clause>& SSS_selections);
	bool is_subset(vector<_clause>& superset, vector<_clause>& subset);
	bool has_any_dependenceRelation_with_any_relevantSCB(unsigned int controller_index);
	
	//methods to create SAT instance:
	void generate_SAT_instance(); //this method is only used with the Retargeting problems when the number of CSUs is "already known" and previously set by the user.
	void generate_incremental_SAT_instance(); //this method is used with the (Retargeting) problems either (first_solution_model) or (optimal_solution_model).
	void delete_previousTF_target_configuration_constraints();
	void update_SAT_instance(const string& input_file); //append additional time frame to the created SAT instance
	bool is_SAT_instance_satisfiable();

	//methods to convert SAT instance into CNF format
	void convert_constraints_to_CNF();
	void convert_constraints_to_CNF_withIDs();

	//methods to find the optimal solution and find the Access time
	unsigned int find_optimal_solution();
	void map_SATAssignmentSolution_to_SATvariables();
	void generate_output_retargeting_vector();
	void compute_no_clockCycles();

	//methods for Retargeting problem
	void first_retargeting_model();
	void first_retargeting_oneCall_model();					//this model is structured based on known and defined no of time frames; that's why it is "one" SAT_Solver call model.
	void first_retargeting_incremental_model();				//this model is structured based on unknown no of time frames; that's why we call the SAT_Solver for "incremetal" times until a solution is found.
	void optimal_retargeting_model();
	
	//associated methods to each time frame
	void starting_configuration_constraints();  //Initial timeframe:
	void subsequent_transitioning_constraints(unsigned int fromTF, unsigned int toTF); //subsequent timeframes
	void target_configuration_constraints(); ////last timeframe
	
	//Auxilary methods
	unsigned int get_SATvariable_no(const string& id, unsigned int timeFrame);
	unsigned int get_length(const string& id);
	void set_SATvariable_assignment(unsigned int SAT_no, bool SAT_value);
	unsigned int get_SATvariable_assignment(const string& id, unsigned int timeFrame);
	bool is_Active_SCB(const string& reg_id, unsigned int TF);
	bool is_Active_TDR(unsigned int selection_clause_index, unsigned int TF);
	bool is_SCB(const string& id);
	string get_negated_string(const string& input);
	unsigned int get_literal_index(const string& node_id);
	void update_ASP_with_scanRegisters_outside_theSearchSpace(unsigned int TF); //this is to set the ASP of all the SCBs out of the SCT
	
	//methods to generate and print output
	void print_file(_SAT_Type option, const string& output_file, const string& file_opening_option);
	void print_vectors_size_capacity_comparison();
	void print_NWstatistics(bool target_statistics, unsigned int index = 0); //true: for "target_reg" statistics, false: for "whole NW" statistics.
	double get_avg(char x); //A->access time, C->CSU cycles, E->execution time, T->Traced nodes
	double get_max(char x);
	double get_total(char x);
};


#endif
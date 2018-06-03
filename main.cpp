#include <fstream>
#include <iostream>
#include <string>
#include <sstream>
#include <vector>
#include <algorithm>
#include <ctype.h>
#define OUTFILENAME "output.bench"

// global counter and constants
int current_wire_index = 0;
int wire_one;
int wire_zero;
int k;
int num_rules;
int s_bits;
int s_start;
int p_out_result;
std::ofstream f(OUTFILENAME);
int mode = 1; // test mode (0) or production mode (1)

std::vector<int> positiveToBinary(int value) {
	std::vector<int> binary;
	if (value == 1 || value == 0) {
		binary.push_back(value);
	}
	else {
		while (value > 0) {
			binary.push_back(value % 2);
			value /= 2;
		}
	}

	while (binary.size() < k) {
		binary.push_back(0);
	}

	return binary;
}

std::vector<int> toBinary(int value) {
	std::vector<int> bin;
	if (value >= 0) {
		bin =  positiveToBinary(value);
	}
	else {
		bin = positiveToBinary(-1 * value);
		for (int i = 0; i < bin.size(); i++) {
			if (bin.at(i) == 1) bin.at(i) = 0;
			else bin.at(i) = 1;
		}
		int i = 0;
		bool flag = true;
		for (i = 0; i < bin.size(); i++) {
			if (bin.at(i) == 0) {
				bin.at(i) = 1;
				for (int j = 0; j < i; j++) {
					bin.at(j) = 0;
				}
				flag = false;
				break;
			}
		}
		if (flag)
			f << "ERROR:OVERFLOW" << std::endl; //THIS CASE SHOULDN"T HAPPEN
	}
	for (int i = 0; i < bin.size(); i++) {
		if (bin.at(i) == 0)bin.at(i) = wire_zero;
		else bin.at(i) = wire_one;
	}
	return bin;
}

int XOR(int A, int B) {
	int notA = current_wire_index++;
	int notB = current_wire_index++;
	int temp_wire1 = current_wire_index++;
	int temp_wire2 = current_wire_index++;
	int out = current_wire_index++;

	f << "G" << notA << " = NOT(G" << A << ")" << std::endl;
	f << "G" << notB << " = NOT(G" << B << ")" << std::endl;
	f << "G" << temp_wire1 << " = NOR(G" << notA << ", G" << notB << ")" << std::endl;
	f << "G" << temp_wire2 << " = NOR(G" << A << ", G" << B << ")" << std::endl;
	f << "G" << out << " = NOR(G" << temp_wire1 << ", G" << temp_wire2 << ")" << std::endl;
	return out;
}

int XNOR(int A, int B) {
	int in = XOR(A, B);
	int out = current_wire_index++;
	f << "G" << out << " = NOT(G" << in << ")" << std::endl;
	return out;
}

std::vector<int> adder(int variable_wire, int constant_wire, int carry_wire) {
	std::vector<int> sum;
	int temp_wire1 = XOR(variable_wire, constant_wire);
	int temp_wire2 = current_wire_index++;
	int temp_wire3 = XOR(temp_wire1, carry_wire);
	int temp_wire4 = current_wire_index++;
	int temp_wire5 = current_wire_index++;
	f << "G" << temp_wire2 << " = AND(G" << variable_wire << ", G" << constant_wire << ")" << std::endl;
	f << "G" << temp_wire4 << " = AND(G" << temp_wire1 << ", G" << carry_wire << ")" << std::endl;
	f << "G" << temp_wire5 << " = OR(G" << temp_wire4 << ", G" << temp_wire2 << ")" << std::endl;
	sum.push_back(temp_wire3);
	sum.push_back(temp_wire5);
	return sum;
}

std::vector<int> adder_N(int variable, int constant) {
	std::vector<int> sum;
	std::vector<int> constant_binary = toBinary(constant);

	int variable_wire = k * variable;
	int carry = wire_zero;
	for(int i = 0; i < k; i++) {
		int constant_wire = constant_binary.at(i);
		std::vector<int> temp = adder(variable_wire++, constant_wire, carry);
		carry = temp.at(1);
		sum.push_back(temp.at(0));
	}

	sum.push_back(carry);
	return sum;
} 

int comparatorGreater(std::vector<int> A, std::vector<int> B) {
	int gtb = wire_zero;
	for (int i = 0; i < k; i++) {
		int a = A.at(i);
		int b = B.at(i);
		int notB = current_wire_index++;
		int gt = current_wire_index++;
		int eq = XNOR(a, b);
		int eqNgtb = current_wire_index++;
		int gtbi = current_wire_index++;
		f << "G" << notB << " = NOT(G" << b << ")" << std::endl;
		f << "G" << gt << " = AND(G" << a << ", G" << notB << ")" << std::endl;
		f << "G" << eqNgtb << " = AND(G" << eq << ", G" << gtb << ")" << std::endl;
		f << "G" << gtbi << " = OR(G" << eqNgtb << ", G" << gt << ")" << std::endl;
		gtb = gtbi;
	}
	return gtb;
}

int comparatorSmaller(std::vector<int> A, std::vector<int> B) {
	return comparatorGreater(B, A);
}

int comparatorSmallerEqual(std::vector<int> A, std::vector<int> B) {
	int isGreater = comparatorGreater(A, B);
	int out = current_wire_index++;
	f << "G" << out << " = NOT(G" << isGreater << ")" << std::endl;
	return out;
}

int comparatorGreaterEqual(std::vector<int> A, std::vector<int> B) {
	int isSmaller = comparatorSmaller(A, B);
	int out = current_wire_index++;
	f << "G" << out << " = NOT(G" << isSmaller << ")" << std::endl;
	return out;
}

int comparatorEqual(std::vector<int> A, std::vector<int> B) {
	int andOut = wire_one;
	for (int i = 0; i < k; i++) {
		int a = A.at(i);
		int b = B.at(i);
		int tempXNOR = XNOR(a, b);
		int tempAND = current_wire_index++;
		f << "G" << tempAND << " = AND(G" << tempXNOR << ", G" << andOut << ")" << std::endl;
		andOut = tempAND;
	}
	return andOut;
}

void multiplexer21(std::vector<int> &in, int out, int s) {
	int notS = current_wire_index++;
	int aOut = current_wire_index++;
	int bOut = current_wire_index++;
	f << "G" << notS << " = NOT(G" << s << ")" << std::endl;
	f << "G" << aOut << " = AND(G" << in.at(0) << ", G" << notS << ")" << std::endl;
	f << "G" << bOut << " = AND(G" << in.at(1) << ", G" << s << ")" << std::endl;
	f << "G" << out << " = OR(G" << aOut << ", G" << bOut << ")" << std::endl;
}

void multiplexerN(std::vector<int> &in, int out, int s) {
	if (in.size() == 2) {
		multiplexer21(in, out, s);
		return;
	}
	int num = in.size() / 2;
	std::vector<int> next_in;
	for (int i = 0; i < num; i++) {
		int temp_out = current_wire_index++;
		std::vector<int> temp;
		temp.push_back(in[2*i]);
		temp.push_back(in[2*i + 1]);
		multiplexer21(temp, temp_out, s);
		next_in.push_back(temp_out);
	}
	multiplexerN(next_in, out, s + 1);
}

void multiplexer(std::vector<int> &in, int out) {
	int in_size = pow(2, s_bits);
	while(in.size() < in_size)in.push_back(wire_zero);
	if (s_bits == 1) {
		multiplexer21(in, out, s_start);
	}
	else {
		multiplexerN(in, out, s_start);
	}
}

std::vector<std::string> split(std::string str, char delimiter) {
	std::vector<std::string> internal;
	std::stringstream ss(str); // Turn the string into a stream.
	std::string tok;
	while (getline(ss, tok, delimiter)) {
		tok.push_back(';');
		internal.push_back(tok);
	}
	return internal;
}

void stringRemoveChars(std::string& str) {
	char chars[] = " \t";
	for (unsigned int i = 0; i < strlen(chars); ++i)
	{
		str.erase(std::remove(str.begin(), str.end(), chars[i]), str.end());
	}
}

int main(int argc, char *argv[]) {
	if (argc != 3) {
		f << "invalid arguments";
		return 0;
	}

	//wires
	k = std::stoi(argv[2]);
	
	std::ifstream fin(argv[1]);
	if (fin.is_open()) {
		std::string skipLine;
		getline(fin, skipLine);

		// count vars
		std::string vars;
		getline(fin, vars);
		int countVars = 0;
		for (int i = 0; i < vars.length(); i++) {
			if (vars[i] == 'x')
				countVars++;
		}

		// print all current state wires
		// f << "# input and output wires" << std::endl;
		if (mode == 0) {
			for (int i = 0; i < countVars; i++) {
				for (int j = 0; j < k; j++) {
					f << "INPUT(G" << current_wire_index++ << ")" << std::endl;
				}
			}

			// print all next state wires
			for (int i = 0; i < countVars; i++) {
				for (int j = 0; j < k; j++) {
					f << "OUTPUT(G" << current_wire_index++ << ")" << std::endl;
				}
			}
		}
		else {
			current_wire_index += 2 * countVars * k;
			for (int i = 0; i < countVars * k; i++) {
				f << "G" << i << " = DFF(G" << countVars * k + i << ")" << std::endl;
			}
		}
		
		// build wire 1 and 0
		f << std::endl << "# building wire 1 and 0" << std::endl;
		f << "INPUT(G" << current_wire_index++ << ")" << std::endl;
		f << "G" << current_wire_index++ << " = NOT(G" << current_wire_index - 2 << ")" << std::endl;
		f << "G" << current_wire_index++ << " = OR(G" << current_wire_index - 2 << ", G" << current_wire_index - 3 << ")" << std::endl;
		wire_one = current_wire_index - 1;
		f << "G" << current_wire_index++ << " = NOT(G" << wire_one << ")" << std::endl;
		wire_zero = current_wire_index - 1;

		getline(fin, skipLine);
		getline(fin, skipLine);

		//start parsing rules

		std::string rule_data;
		std::string tempStr;
		while(getline(fin, tempStr)) {
			rule_data += tempStr;
		} 

		//trim out init and target statements
		for (int i = rule_data.length() - 1; i > 0; i--) {
			if (rule_data.at(i) == ';') {
				rule_data.resize(i + 1);
				break;
			}
		}

		std::vector<std::vector<std::vector<int>>> Qs_out(countVars, std::vector<std::vector<int> >(rule_data.size(), std::vector <int>(k, -1)));
		std::vector<int> ps_outs;

		// a vector of rules
		// each rule has Ps -> imply Qs
		std::vector<std::string> rules = split(rule_data, ';');
		// computer selector size
		num_rules = rules.size();
		s_bits = ceil(log2(num_rules));
		if (s_bits == 0) s_bits++;
		s_start = current_wire_index;
		f << std::endl << "# selector" << std::endl;
		for (int i = 0; i < s_bits; i++) {
			f << "INPUT(G" << current_wire_index++ << ")" << std::endl;
		}

		p_out_result = current_wire_index++;
		f << "OUTPUT(G" << p_out_result << ")" << std::endl;


		for (int i = 0; i < rules.size(); i++) {
			f << std::endl << "# Rule: " << i << std::endl;
			// split each rule to Ps and Qs
			std::string rule = rules[i];
			std::vector<std::string> Ps;
			std::vector<std::string> Qs;
			bool isP = true;
			int lastIndex = 0;
			for (int j = 0; j < rule.length(); j++) {
				if (rule.at(j) == ',' || rule.at(j) == ';' || (rule.at(j) == '-' && rule.at(j + 1)=='>')){
					if (rule.at(j) == '-' && rule.at(j + 1) == '>') {
						isP = false;
						std::string add_str = rule.substr(lastIndex, j - lastIndex - 1);
						stringRemoveChars(std::ref(add_str));
						if (add_str.length() != 0 && j - lastIndex - 1 > 0) {
							Ps.push_back(add_str);
						}
					}
					else {
						if (isP) {
							std::string add_str = rule.substr(lastIndex, j - lastIndex);
							stringRemoveChars(std::ref(add_str));
							if (add_str.length() != 0) {
								Ps.push_back(add_str);
							}
						}
						else {
							std::string add_str = rule.substr(lastIndex, j - lastIndex);
							stringRemoveChars(std::ref(add_str));
							if (add_str.length() != 0) {
								Qs.push_back(add_str);
							}
						}
					}

					while (j < rule.length() && rule.at(j) != 'x') j++;
					lastIndex = j;
					j--;
				}
			}

			/*
			for (int j = 0; j < Ps.size(); j++) {
				f << Ps.at(j) << std::endl;
			}
			for (int j = 0; j < Qs.size(); j++) {
				f << Qs.at(j) << std::endl;
			}
			*/

			// all Ps will be ANDed together to determine whether Qs would be executed
			std::vector<int> ps_out;
			for (int j = 0; j < Ps.size(); j++) {
				//ADD RESULT TO PS_OUT
				std::string p = Ps.at(j);
				int index = 1;
				int isSecondConstantOrVariable = 0;
				while (isdigit(p.at(index++)));
				int a = atoi(p.substr(1, index - 1).c_str());
				while (!isdigit(p.at(index++)));
				int b  = atoi(p.substr(index - 1, p.length()).c_str());
				if (p.at(index - 2) == 'x') isSecondConstantOrVariable = 1;
				std::vector<int> a_vec;
				std::vector<int> b_vec;
				int a_vec_index = k * a;
				int b_vec_index = 0;
				if (isSecondConstantOrVariable == 1) {
					b_vec_index = k * b;
					for (int t = 0; t < k; t++) {
						b_vec.push_back(b_vec_index++);
					}
				}
				else {
					b_vec = toBinary(b);
				}
				for (int t = 0; t < k; t++) {
					a_vec.push_back(a_vec_index++);
				}

				if (p.find(">=") != -1) {
					ps_out.push_back(comparatorGreaterEqual(a_vec, b_vec));
				}
				else if (p.find("<=") != -1) {
					ps_out.push_back(comparatorSmallerEqual(a_vec, b_vec));
				}
				else if (p.find("==") != -1) {
					ps_out.push_back(comparatorEqual(a_vec, b_vec));
				}
				else if (p.find(">") != -1) {
					ps_out.push_back(comparatorGreater(a_vec, b_vec));
				}
				else if (p.find("<") != -1) {
					ps_out.push_back(comparatorSmaller(a_vec, b_vec));
				}
				else {
					f << "# ERROR" << std::endl;
				}
			}

			//AND everything in PS_OUT with wire_one
			f << std::endl << "# AND PS_OUT" << std::endl;
			int wire_ps_out_and ; 
			int wire_ps_out_and_temp = wire_one;
			for (int j = 0; j < ps_out.size(); j++) {
				wire_ps_out_and = current_wire_index++;
				f << "G" << wire_ps_out_and << " = AND(G" << wire_ps_out_and_temp << ", G" << ps_out.at(j) << ")" << std::endl;
				wire_ps_out_and_temp = wire_ps_out_and;
			}
			
			if (ps_out.size() != 0)
				ps_outs.push_back(wire_ps_out_and);
			else {
				ps_outs.push_back(wire_one);
			}


			// now wire_one can be used for multiplexer to determin if Qs will be executed
			std::vector<int> carries;
			for (int j = 0; j < Qs.size(); j++) {
				std::string q = Qs.at(j);
				int currentVariable = q.at(1) - '0';
				int variable_index = 1;
				while (q.at(variable_index) != 39) {
					variable_index++;
				}
				int variable = atoi(q.substr(1, variable_index).c_str());
				f << std::endl << "# Adder for variable " << variable << std::endl;
				while (q.at(variable_index) != '-' && q.at(variable_index) != '+') {
					variable_index++;
				}

				int constant;
				if (q.at(variable_index) == '-') {
					constant = atoi(q.substr(variable_index, q.length()).c_str());
				}
				else {
					constant = atoi(q.substr(variable_index+1, q.length()).c_str());
				}
				
				//the last element in sum is the carry bit
				std::vector<int> sum = adder_N(variable, constant);
				for (int t = 0; t < sum.size() - 1; t++) {
					Qs_out[currentVariable][i][t] = sum.at(t);
				}
				carries.push_back(sum.back());
			}

			f << std::endl << "# anding carries with Ps_out" << std::endl;
			int p_out = ps_outs.back();
			ps_outs.pop_back();
			for (int j = 0; j < carries.size(); j++) {
				int carry = carries.at(j);
				int notC = current_wire_index++;
				int andC = current_wire_index++;
				f << "G" << notC << " = NOT(G" << carry << ")" << std::endl;
				f << "G" << andC << " = AND(G" << p_out << ", G" << notC << ")" << std::endl;
				p_out = andC;
			}
			ps_outs.push_back(p_out);
		} // end of a rule
		

		int in_size = pow(2, s_bits);
		while (ps_outs.size() < in_size)ps_outs.push_back(wire_zero);
		std::cout << ps_outs.size();

		//Now select Ps out
		f << std::endl << "# multiplexer for Ps_out" << std::endl;
		multiplexer(ps_outs, p_out_result);
		for (int i = 0; i < countVars; i++) {
			for (int t = 0; t < k; t++) {
				std::vector<int> variable_bit;
				for (int j = 0; j < num_rules; j++) {
					if (Qs_out[i][j][t] == -1) {
						//std::cout << i * k + t << std::endl;
						variable_bit.push_back(i * k + t);
					}else
						variable_bit.push_back(Qs_out[i][j][t]);
				}

				
				int out = countVars*k + i*k + t;
				f << std::endl << "# mutiplexer for variable " << i << " bit " << t << std::endl;
				//multiplexer(variable_bit, out);
				
				int tempOut = current_wire_index++;
				multiplexer(variable_bit, tempOut);
				// if P not satisfied, keep original value
				std::vector<int> tv;
				tv.push_back(i*k + t);
				tv.push_back(tempOut);
				multiplexer21(tv, out, p_out_result);
				
			}
		}
		
	}
	else {
		f << "Input file name is invalid." << std::endl;
	}

	int pause;
	std::cout << "Done";
	std::cin >> pause;
	return 0;
}

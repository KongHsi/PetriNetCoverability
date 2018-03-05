#include <fstream>
#include <iostream>
#include <string>
#include <sstream>
#include <vector>
#include <algorithm>
#include <ctype.h>

// modify this part when testing a new file because every file is different
#define CIRCUIT_FILE "C:\\Users\\Richard\\source\\repos\\petrinet2circuit\\petrinet2circuit\\output.txt"
#define SPEC_FILE "C:\\Users\\Richard\\source\\repos\\petrinet2circuit\\petrinet2circuit\\test.spec"
const int max_lines = 500;
const int k = 4;
const int num_inout = 3;
const int s_start = 28;
const int num_s = 2;
const int out_wire = 30;

void pause() {
	int a;
	std::cin >> a;
}

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

	while (binary.size() < 4) {
		binary.push_back(0);
	}

	return binary;
}

std::vector<int> toBinary(int value) {
	std::vector<int> bin;
	if (value >= 0) {
		bin = positiveToBinary(value);
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
	}
	for (int i = 0; i < bin.size(); i++) {
		if (bin.at(i) == 0)bin.at(i) = 0;
		else bin.at(i) = 1;
	}
	return bin;
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

void str2int(std::vector<int>& arr, std::string in) {
	int start = -1;
	int current = 0;
	for (int i = 0; i < in.length(); i++) {
		if (isdigit(in.at(i))) {
			if (start == -1)
				start = i;
		}
		else {
			if (start != -1) {
				std::string temp = in.substr(start, i - start);
				arr.push_back(atoi(temp.c_str()));
				start = -1;
			}
		}
	}
}

std::vector<int> testCircuit(std::vector<int>& arr_in) {
	std::ifstream fin(CIRCUIT_FILE);
	int arr[max_lines] = { 0 };
	for (int i = 0; i < num_inout * k; i++) {
		arr[i] = arr_in[i];
	}

	int tt = num_inout * k;
	for (int i = s_start; i < s_start + num_s; i++) {
		arr[i] = arr_in[tt++];
	}

	std::string s;
	while (getline(fin, s)) {
		if (s.size() == 0 || s.at(0) == '#') {}
		else if (s.find("NOT") != -1) {
			std::vector<int> vec;
			str2int(vec, s);
			int a = vec.at(0);
			int b = vec.at(1);
			if (arr[b] == 0)arr[a] = 1;
			else arr[a] = 0;
		}
		else if (s.find("XNOR") != -1) {
			std::vector<int> vec;
			str2int(vec, s);
			int a = vec.at(0);
			int b = vec.at(1);
			int c = vec.at(2);
			int t = (arr[b] ^ arr[c]);
			if (t == 0)arr[a] = 1;
			else arr[a] = 0;
		}
		else if (s.find("XOR") != -1) {
			std::vector<int> vec;
			str2int(vec, s);
			int a = vec.at(0);
			int b = vec.at(1);
			int c = vec.at(2);
			arr[a] = (arr[b] ^ arr[c]);
		}
		else if (s.find("OR") != -1) {
			std::vector<int> vec;
			str2int(vec, s);
			int a = vec.at(0);
			int b = vec.at(1);
			int c = vec.at(2);
			arr[a] = arr[b] | arr[c];
		}
		else if (s.find("AND") != -1) {
			std::vector<int> vec;
			str2int(vec, s);
			int a = vec.at(0);
			int b = vec.at(1);
			int c = vec.at(2);
			arr[a] = arr[b] & arr[c];
		}

	}
	
	std::vector<int> out;
	for (int i = num_inout * k; i < num_inout * k * 2; i++) {
		out.push_back(arr[i]);
	}
	out.push_back(arr[out_wire]);
	return out;
}

std::vector<int> testLogic(std::vector<int> in) {
	int select = in.back();
	in.pop_back();

	std::ifstream fin(SPEC_FILE);
	if (fin.is_open()) {
		std::string skipLine;
		getline(fin, skipLine);

		std::string vars;
		getline(fin, vars);

		int countVars = 0;
		for (int i = 0; i < vars.length(); i++) {
			if (vars[i] == 'x')
				countVars++;
		}

		getline(fin, skipLine);
		getline(fin, skipLine);

		//start parsing rules
		std::string rule_data;
		std::string tempStr;
		while (getline(fin, tempStr)) {
			rule_data += tempStr;
		}

		//trim out init and target statements
		for (int i = rule_data.length() - 1; i > 0; i--) {
			if (rule_data.at(i) == ';') {
				rule_data.resize(i + 1);
				break;
			}
		}

		std::vector<std::string> rules = split(rule_data, ';');

		if (select >= rules.size()) {
			std::vector<int> out;
			for (int i = 0; i < in.size(); i++) {
				out.push_back(0);
			}
			out.push_back(0);
			return out;
		}

		// split each rule to Ps and Qs
		std::string rule = rules[select];
		std::vector<std::string> Ps;
		std::vector<std::string> Qs;
		bool isP = true;
		int lastIndex = 0;
		for (int j = 0; j < rule.length(); j++) {
			if (rule.at(j) == ',' || rule.at(j) == ';' || (rule.at(j) == '-' && rule.at(j + 1) == '>')) {
				if (rule.at(j) == '-' && rule.at(j + 1) == '>') {
					isP = false;
					std::string add_str = rule.substr(lastIndex, j - lastIndex - 1);
					stringRemoveChars(std::ref(add_str));
					if (add_str.length() != 0) {
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

		bool p_satisfied = true;
		for (int i = 0; i < Ps.size(); i++) {
			std::string p = Ps.at(i);
			int isSecondConstantOrVariable = 0;
			int index = 1;
			while (isdigit(p.at(index++)));
			int a = atoi(p.substr(1, index - 1).c_str());
			while (!isdigit(p.at(index++)));
			int b = atoi(p.substr(index - 1, p.length()).c_str());
			if (p.at(index - 2) == 'x') isSecondConstantOrVariable = 1;


			if (p.find(">=") != -1) {
				if (in.at(a) < b)
					p_satisfied = false;
			}
			else if (p.find("<=") != -1) {
				if (in.at(a) > b)
					p_satisfied = false;
			}
			else if (p.find("==") != -1) {
				if (in.at(a) != b)
					p_satisfied = false;
			}
			else if (p.find(">") != -1) {
				if (in.at(a) <= b)
					p_satisfied = false;
			}
			else if (p.find("<") != -1) {
				if (in.at(a) >= b)
					p_satisfied = false;
			}
			else {
				std::cout << "# ERROR" << std::endl;
			}
		}


			for (int j = 0; j < Qs.size(); j++) {
				std::string q = Qs.at(j);
				int currentVariable = q.at(1) - '0';
				int variable_index = 1;
				while (q.at(variable_index) != 39) {
					variable_index++;
				}
				int variable = atoi(q.substr(1, variable_index).c_str());
				while (q.at(variable_index) != '-' && q.at(variable_index) != '+') {
					variable_index++;
				}

				int constant;
				if (q.at(variable_index) == '-') {
					constant = atoi(q.substr(variable_index, q.length()).c_str());
				}
				else {
					constant = atoi(q.substr(variable_index + 1, q.length()).c_str());
				}
				in[variable] += constant;
			}

		std::vector<int> out;
		for (int i = 0; i < in.size(); i++) {
			out.push_back(in[i]);
		}
		out.push_back(p_satisfied == true ? 1 : 0);
		return out;
	}
}

bool enumerate(std::vector<int> &c_array) {
	/*
	for (int i = 0; i < c_array.size(); i++) {
		std::cout << c_array[i] << " ";
	}
	std::cout << std::endl;
	*/

	if (c_array.back() < k - 1) {
		c_array.back()++;
		return true;
	}

	for (int i = c_array.size() - 2; i >= 0; i--) {
		if (c_array[i] < k - 1) {
			c_array[i]++;
			for (int j = i + 1; j < c_array.size(); j++) {
				c_array[j] = 0;
			}
			return true;
		}
	}

	return false;
}

int main(int argc, char *argv[]) {

	//create test inputs - size #inputs + 1 selector
	std::vector<int> c_array;
	for (int i = 0; i < num_inout; i++) {
		c_array.push_back(0);
	}
	c_array.push_back(0);

	do {
		std::vector<int> arr(num_inout * k + num_s);
		for (int i = 0; i < num_inout; i++) {
			std::vector<int> t = toBinary(c_array[i]);
			for (int j = 0; j < k; j++) {
				arr[i * k + j] = t.at(j);
			}
		}
		std::vector<int> t = toBinary(c_array[3]);
		for (int i = 0; i < num_s; i++) {
			arr[num_inout * k + i] = t.at(i);
		}

		std::vector<int> circuitOut = testCircuit(arr);
		std::vector<int> out = testLogic(c_array);

		std::vector<int> logicOut;
		for (int i = 0; i < out.size() - 1; i++) {
			std::vector<int> temp = toBinary(out.at(i));
			for (int j = 0; j < k; j++)
				logicOut.push_back(temp.at(j));
		}
		logicOut.push_back(out.at(out.size() - 1));

		if (circuitOut.size() != logicOut.size())
			std::cout << "False - size" << std::endl;
		for (int i = 0; i < circuitOut.size(); i++) {
			if (circuitOut.at(i) != logicOut.at(i)) {
				for (int i = 0; i < num_inout * k + 1; i++) {
					std::cout << circuitOut.at(i) << " : " << logicOut.at(i) << "---" << arr[i] << std::endl;
				}
				std::cout << "False" << std::endl;
				pause();
			}
		}
		
	} while (enumerate(c_array));

	std::cout << "Passed" << std::endl;
	pause();
}
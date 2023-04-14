#include "return_codes.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
double* house(double* matrix1, double* temp, double* vech, double* d, double* sums, size_t n, size_t n2)
{
	for (int i = 0; i < n; i++)
	{
		double sum = 0;
		for (int j = i; j < n; j++)
		{
			vech[i * n2 + j] = 0;
			sum += matrix1[j * n2 + i] * matrix1[j * n2 + i];
		}
		if (matrix1[i * n2 + i] > 0)
		{
			sum = sqrt(sum);
		}
		else
		{
			sum = -sqrt(sum);
		}
		double del =
			sum * sum - matrix1[i * n2 + i] * matrix1[i * n2 + i] + (sum + matrix1[i * n2 + i]) * (sum + matrix1[i * n2 + i]);
		del = sqrt(del);
		if (del == 0)
		{
			d[i] = 1;
			continue;
		}
		for (int j = 0; j < n; j++)
		{
			vech[i * n2 + j] = matrix1[j * n2 + i];
			sums[j] = 0;
		}
		vech[i * n2 + i] += sum;
		for (int j = i; j < (i + 2 < n ? i + 2 : n); j++)
		{
			for (int k = i; k < n; k++)
			{
				temp[j * n2 + k] = matrix1[j * n2 + k];
				matrix1[j * n2 + k] = matrix1[j * n2 + k] * vech[i * n2 + j] / del;
				sums[k] += matrix1[j * n2 + k];
			}
		}
		for (int j = i; j < (i + 2 < n ? i + 2 : n); j++)
		{
			for (int k = i; k < n; k++)
			{
				matrix1[j * n2 + k] = temp[j * n2 + k] * del - (2 * vech[i * n2 + j] * sums[k]);
				matrix1[j * n2 + k] /= del;
			}
		}
		d[i] = del;
	}
	return matrix1;
}
double* buildRQ(const double* h, double* matrix, const double* del, size_t n, size_t n2)
{
	for (int i = 0; i < n; i++)
	{
		for (int j = 0; j < n; j++)
		{
			double s = 0;
			for (int k = i; k < (i + 2 < n ? i + 2 : n); k++)
			{
				double old = matrix[j * n2 + k];
				if (k == i)
				{
					for (int l = i; l < (i + 2 < n ? i + 2 : n); l++)
					{
						s = s + matrix[j * n2 + l] * h[i * n2 + l] / del[i];
					}
					matrix[j * n2 + k] = s;
				}
				matrix[j * n2 + k] = s;
				matrix[j * n2 + k] = (old * del[i] - 2 * matrix[j * n2 + k] * h[i * n2 + k]) / del[i];
			}
		}
	}
	return matrix;
}

struct PAIR
{
	double first;
	double second;
	int compl ;
};

struct PAIR solve2x2(const double* m, size_t i, size_t j, size_t n2)
{
	double a = m[i * n2 + j];
	double b = m[i * n2 + j + 1];
	double c = m[(i + 1) * n2 + j];
	double d = m[(i + 1) * n2 + j + 1];
	double dis = (a + d) * (a + d) - 4 * a * d + 4 * b * c;
	if (dis < 0)
	{
		struct PAIR n = { .first = (a + d) / 2, .second = sqrt(-dis) / 2, 1 };
		return n;
	}
	else
	{
		struct PAIR n = { .first = ((a + d) - sqrt(dis)) / 2, .second = ((a + d) + sqrt(dis)) / 2, 0 };
		return n;
	}
}
double hesenberg(double* matrix1, double* vec, double* temp1, double* sums, size_t n, size_t n2)
{
	double delta = 1000;
	for (int i = 0; i < (n == 1 ? 0 : n - 2); i++)
	{
		double a = 0;
		for (int j = i + 1; j < n; j++)
		{
			a += matrix1[j * n2 + i] * matrix1[j * n2 + i];
		}
		if (matrix1[(i + 1) * n2 + i] > 0)
		{
			a = -sqrt(a);
		}
		else
		{
			a = sqrt(a);
		}
		double r = ((a * a) - matrix1[(i + 1) * n2 + i] * a) / 2;
		r = sqrt(r);
		if (r == 0)
		{
			continue;
		}
		for (int j = 0; j < n; j++)
		{
			if (j <= i)
			{
				vec[j] = 0;
			}
			else if (j == i + 1)
			{
				vec[j] = (matrix1[(i + 1) * n2 + i] - a) / (2 * r);
			}
			else
			{
				vec[j] = matrix1[j * n2 + i] / (2 * r);
			}
			sums[j] = 0;
		}
		for (int j = 0; j < n; j++)
		{
			double s = 0;
			for (int k = i; k < n; k++)
			{
				double old = matrix1[j * n2 + k];
				if (k == i)
				{
					for (int l = 0; l < n; l++)
					{
						s = s + matrix1[j * n2 + l] * vec[l];
					}
					matrix1[j * n2 + k] = s;
				}
				else
				{
					matrix1[j * n2 + k] = s;
				}
				matrix1[j * n2 + k] = (old - 2 * matrix1[j * n2 + k] * vec[k]);
			}
		}
		for (int j = 0; j < n; j++)
		{
			for (int k = 0; k < n; k++)
			{
				temp1[j * n2 + k] = matrix1[j * n2 + k];
				matrix1[j * n2 + k] = matrix1[j * n2 + k] * vec[j];
				sums[k] += matrix1[j * n2 + k];
			}
		}
		for (int j = 0; j < n; j++)
		{
			for (int k = 0; k < n; k++)
			{
				matrix1[j * n2 + k] = temp1[j * n2 + k] - (2 * vec[j] * sums[k]);
				if (i >= n - 3 && fabs(matrix1[j * n2 + k]) < delta)
				{
					delta = fabs(matrix1[j * n2 + k]);
				}
			}
		}
	}
	return delta;
}
size_t householderQR(double* matrix1, double* temp, double* temp2, double* del, double* res, double* sums, size_t n, size_t n2, double delta)
{
	size_t it = 0;
	struct PAIR oldRes = { 0, 0, 0 };
	if (n == 2)
	{
		struct PAIR ans = solve2x2(matrix1, 0, 0, n2);
		if (ans.compl == 0)
		{
			res[0] = ans.first;
			res[1] = 0;
			res[2] = ans.second;
			res[3] = 0;
			it += 4;
		}
		else
		{
			res[0] = ans.first;
			res[1] = ans.second;
			it += 2;
		}
		return it;
	}
	while (n > 1)
	{
		double shift = matrix1[(n - 1) * n2 + n - 1];
		if (fabs(matrix1[(n - 1) * n2 + n - 2] - matrix1[(n - 2) * n2 + n - 1]) < 5e-300)
		{
			double b = matrix1[(n - 2) * n2 + n - 2] - matrix1[(n - 1) * n2 + n - 1] / 2;
			double bm1 = matrix1[(n - 1) * n2 + n - 2];
			shift = bm1 * bm1 / (fabs(b) + sqrt(b * b + bm1 * bm1));
			if (b > 0)
			{
				shift = matrix1[(n - 1) * n2 + n - 1] - shift;
			}
			else if (b < 0)
			{
				shift = matrix1[(n - 1) * n2 + n - 1] + shift;
			}
			else
			{
				shift = matrix1[(n - 1) * n2 + n - 1];
			}
		}
		for (int j = 0; j < n2; j++)
		{
			matrix1[j * n2 + j] -= shift;
		}
		house(matrix1, temp, temp2, del, sums, n, n2);
		buildRQ(temp2, matrix1, del, n, n2);
		for (int j = 0; j < n2; j++)
		{
			matrix1[j * n2 + j] += shift;
		}
		if (fabs(matrix1[(n - 1) * n2 + n - 2]) < delta)
		{
			res[it] = matrix1[(n - 1) * n2 + n - 1];
			matrix1[(n - 1) * n2 + n - 2] = 0;
			res[it + 1] = 0;
			it += 2;
			n--;
		}
		else
		{
			struct PAIR nu = solve2x2(matrix1, n - 2, n - 2, n2);
			if (nu.compl &&oldRes.compl &&fabs((oldRes.first - nu.first)) < delta && fabs((oldRes.second - nu.second)) < delta)
			{
				res[it] = nu.first;
				res[it + 1] = nu.second;
				it += 2;
				n -= 2;
				if (n > 1)
				{
					oldRes = solve2x2(matrix1, n - 2, n - 2, n2);
				}
			}
			else
			{
				oldRes = nu;
			}
		}
	}
	if (n > 0)
	{
		res[it] = matrix1[0];
		res[it + 1] = 0;
		it += 2;
	}
	return it;
}
int check(double* matrix1, double* temp2, double* temp, double* del, double* ans, double* sums)
{
	if (!matrix1 || !temp2 || !temp || !del || !ans || !sums)
	{
		if (temp2)
		{
			free(temp2);
		}
		if (temp)
		{
			free(temp);
		}
		if (del)
		{
			free(del);
		}
		if (ans)
		{
			free(ans);
		}
		if (matrix1)
		{
			free(matrix1);
		}
		if (sums)
		{
			free(sums);
		}
		return ERROR_OUT_OF_MEMORY;
	}
	return SUCCESS;
}
void writeFile(FILE* f, double* ans, size_t n)
{
	for (int i = 0; i < n; i += 2)
	{
		if (ans[i + 1] == 0)
		{
			fprintf(f, "%g\n", ans[i]);
		}
		else
		{
			fprintf(f, "%g +%gi\n", ans[i], ans[i + 1]);
			fprintf(f, "%g -%gi\n", ans[i], ans[i + 1]);
		}
	}
}
void freeAll(double* matrix1, double* temp2, double* temp, double* del, double* ans, double* sums)
{
	free(matrix1);
	free(temp2);
	free(temp);
	free(del);
	free(ans);
	free(sums);
}

int main(int argv, char* argc[])
{
	if (argv != 3)
	{
		fprintf(stderr, "Wrong number of arguments, expected 2\n");
		return ERROR_PARAMETER_INVALID;
	}
	FILE* f = fopen(argc[1], "r");
	if (!f)
	{
		fprintf(stderr, "Can't open input file %s\n", argc[1]);
		return ERROR_CANNOT_OPEN_FILE;
	}
	size_t n;
	fscanf(f, "%zi", &n);
	double* matrix1 = malloc(sizeof(double) * n * n);
	double* temp2 = malloc(sizeof(double) * n * n);
	double* temp = malloc(sizeof(double) * n * n);
	double* del = malloc(sizeof(double) * n);
	double* ans = malloc(sizeof(double) * 2 * n);
	double* sums = malloc(sizeof(double) * n);
	int rCode = check(matrix1, temp2, temp, del, ans, sums);
	if (rCode != SUCCESS)
	{
		fclose(f);
		fprintf(stderr, "Not enough memory, memory allocation failed\n");
		return rCode;
	}
	for (int i = 0; i < n; i++)
	{
		for (int j = 0; j < n; j++)
		{
			fscanf(f, "%lf", &matrix1[i * n + j]);
		}
	}
	fclose(f);
	double delta;
	delta = hesenberg(matrix1, del, temp, temp2, n, n);
	delta *= 1e-9;
	delta = delta > 1e-8 ? delta : 1e-8;
	size_t it = householderQR(matrix1, temp, temp2, del, ans, sums, n, n, delta);
	f = fopen(argc[2], "w");
	if (!f)
	{
		freeAll(matrix1, temp2, temp, del, ans, sums);
		fprintf(stderr, "Can't open output file %s\n", argc[2]);
		return ERROR_CANNOT_OPEN_FILE;
	}
	writeFile(f, ans, it);
	fclose(f);
	freeAll(matrix1, temp2, temp, del, ans, sums);
	return SUCCESS;
}

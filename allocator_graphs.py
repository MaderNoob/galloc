import matplotlib.pyplot as plt
import glob
import itertools
import os

BENCHMARK_RESULTS_DIR = 'benchmark_results/'
BENCHMARK_RESULT_GRAPHS_DIR = 'benchmark_result_graphs/'

def get_benchmark_data(filename):
    with open(filename, 'r') as f:
        rows = f.readlines()
    allocators = {}
    for row in rows:
        lst = row.split(',')
        allocators[lst[0]] = [float(i) for i in lst[1:]]
    return allocators

def plot_benchmark(filename):
    xaxis = [i/10 for i in range(1, 10+1)]
    data = get_benchmark_data(filename)
    yvalues = []
    for k,v in data.items():
        plt.plot(xaxis, v, label=k)
        yvalues.append(v)
    plt.legend()
    test_name = filename[len(BENCHMARK_RESULTS_DIR): filename.find('.csv')]    
    plt.title(test_name)
    plt.xlabel('time (seconds)\n')
    plt.ylabel('actions')
    
    full_diff_str = ''
    
    k1 = 'galloc'
    for k2 in list(data.keys())[1:]:
        v1 = data[k1]
        v2 = data[k2]
        diff = round(difference_average(v1, v2), 2)    
        full_diff_str += f'{k1} - {k2}: {diff}%\n'
            
    plt.figtext(0.133, 0.75, full_diff_str, fontsize=10)
            
    plt.savefig(BENCHMARK_RESULT_GRAPHS_DIR + test_name + '.png')
    plt.show()

def percentage_difference(a,b):
    return (a -b)/(b/2) * 100

def difference_average(plt_a, plt_b):
    differences = []
    for a, b in zip(plt_a, plt_b):
        differences.append(percentage_difference(a,b))
    return sum(differences)/len(differences)

def main():
    if not os.path.exists(BENCHMARK_RESULTS_DIR):
        os.mkdir(BENCHMARK_RESULT_GRAPHS_DIR)
    for filename in glob.glob(BENCHMARK_RESULTS_DIR+'*.*'):
        plot_benchmark(filename)

if __name__ == '__main__':
    main()
    print('done')

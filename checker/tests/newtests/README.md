# Running SPIN tests

## Run tests

```sh
./collect_results.sh
```
- `collect_results.sh`: choose which benchmarks to run
- `run_spin.sh`: runs a single benchmark with the given parameters

## Generate csv

```sh
./parse_logs.sh
```

- `parse_logs.sh`: parses the SPIN logs from the various sub-folders of the
  `results/` folder, and creates a single csv file named `spin_results.sh`
  that contain all the runs

## Prepare the latex table

```sh
./parse_csv.sh
```

- `parse_csv.sh`: creates a LaTeX table by parsing the `spin_results.csv` file
  and only keeping the relevant columns


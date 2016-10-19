BEGIN {
    FS="\t";
    hard_error = 0;
}

NR > 1 {
    if ($7 == 42) {
        soft_error[$1] = 1;
    } else if ($7 != 0) {
        hard_error = 1;
        exit 1;
    } else {
        soft_error[$1] = 0;
    }
}

END {
    if (hard_error == 1) {
        exit 1;
    }

    for (i in soft_error) {
        if (soft_error[i] == 0) {
            printf("%d\n", i);
        }
    }

    exit 0;
}


#ifndef	_SBI_ERROR_H
#define	_SBI_ERROR_H

#define SBI_OK		0
#define SBI_EUNKNOWN	-1
#define SBI_EFAIL	-2
#define SBI_EINVAL	-3
#define SBI_ENOENT	-4
#define SBI_ENOTSUPP	-5
#define SBI_ENODEV	-6
#define SBI_ENOSYS	-7
#define SBI_ETIMEDOUT	-8
#define SBI_EIO		-9
#define SBI_EILL	-10

/* SBI v0.2+ standard return codes. */
#define SBI_SUCCESS			0
#define SBI_ERR_FAILED			-1
#define SBI_ERR_NOT_SUPPORTED		-2
#define SBI_ERR_INVALID_PARAM		-3
#define SBI_ERR_DENIED			-4
#define SBI_ERR_INVALID_ADDRESS		-5
#define SBI_ERR_ALREADY_AVAILABLE	-6
#define SBI_ERR_ALREADY_STARTED		-7
#define SBI_ERR_ALREADY_STOPPED		-8
#define SBI_ERR_NO_SHMEM		-9
#define SBI_ERR_INVALID_STATE		-10
#define SBI_ERR_BAD_RANGE		-11
#define SBI_ERR_TIMEOUT			-12
#define SBI_ERR_IO			-13
#define SBI_ERR_DENIED_LOCKED		-14

#endif
